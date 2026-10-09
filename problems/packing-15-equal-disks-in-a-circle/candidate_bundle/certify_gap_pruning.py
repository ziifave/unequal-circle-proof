#!/usr/bin/env python3
"""Exact-rational certificate and exhaustive dihedral bracelet pruning for 15 equal disks.
No floating-point arithmetic and no external dependencies.
Mathematical meaning: only the 117 eliminated dihedral patterns are proved impossible.
Remaining patterns are UNKNOWN, not claimed feasible or impossible.
"""
from fractions import Fraction as F
from collections import Counter
import json

N=15
ONE=F(1)

def sin_upper(x):
    # 0<=x<=1: alternating Maclaurin upper bound
    assert F(0)<=x<=F(1)
    return x-x**3/F(6)+x**5/F(120)

def cos_lower(x):
    # 0<=x<=1: alternating Maclaurin lower bound
    assert F(0)<=x<=F(1)
    return ONE-x**2/F(2)

# cot(pi/5)^2 = 1 + 2/sqrt(5) exactly.
# sqrt(5)>559/250 because (559/250)^2<5.
assert F(559,250)**2<F(5)
cot_ub=F(1377,1000)
assert ONE+F(500,559)<cot_ub**2
# b0^2 = 1+(2+cot(pi/5))^2, b0 < 1761/500.
B=F(1761,500)
assert ONE+(2+cot_ub)**2<B**2
# L0=b0 - 4/b0 < B-4/B by strict monotonicity.
LUB=B-F(4)/B
assert LUB < F(12,5)  # L0 < 2.4
# theta0=2*asin(1/b0) > 23/40.
# sin(23/80) < 1/B <1/b0.
assert sin_upper(F(23,80))<ONE/B
# gamma0=2*asin(1/L0)>43/50.  sin(43/100)<1/LUB.
assert sin_upper(F(43,100))<ONE/LUB
# alpha0=angle(5/3,b0)>3/10.
# cos(3/10)>=cos_lower(3/10)>(a^2+B^2-4)/(2*a*B).
a=F(5,3)
cB=(a*a+B*B-F(4))/(2*a*B)
assert cos_lower(F(3,10))>cB

THETA_LO=F(23,40)
GAMMA_LO=F(43,50)
ALPHA_LO=F(3,10)
# G_m=2pi-(m-1)theta0, and pi < 22/7.
cap_ub=lambda m:F(44,7)-(m-1)*THETA_LO
assert ALPHA_LO+GAMMA_LO>cap_ub(10)
assert F(6,5)>cap_ub(10) # phi(5/3,5/3)=2asin(3/5)>6/5
assert 2*GAMMA_LO>cap_ub(9)
assert 3*GAMMA_LO>cap_ub(8)
assert 4*GAMMA_LO>cap_ub(7)

# For a gap of the m outer disks, all but at most one inner disk have radius>=1.
# m=10: at most one regular (=radius>=1) in each gap: proved by
#          the 5/3 split using ALPHA_LO+GAMMA_LO and 6/5.
# m=9 : at most two regular per gap since 2*GAMMA_LO>G_9.
# m=8 : at most three regular per gap since 3*GAMMA_LO>G_8.
# m=7 : at most four regular per gap since 4*GAMMA_LO>G_7.
# Each run of t consecutive 'I' symbols between outer disks has at least t-1
# regular inner circles. Therefore run<=cap_regular+1, and any run of
# length==cap_regular+1 consumes the unique exceptional radius<1,
# so at most one such run can occur.

def canonical_dihedral(bits):
    return min(tuple(s[k:]+s[:k])
               for s in (bits,bits[::-1]) for k in range(N))

def inner_runs(bits):
    j=bits.index(0)
    seq=[bits[(j+1+k)%N] for k in range(N)]
    ret=[];cnt=0
    for v in seq:
        if v:cnt+=1
        elif cnt:ret.append(cnt);cnt=0
    if cnt:ret.append(cnt)
    return ret

results=[]
all_eliminated=[]
remaining={}
for k in (5,6,7,8):
    seen=set()
    for mask in range(1<<N):
        if mask.bit_count()==k:
            s=[(mask>>i)&1 for i in range(N)]
            seen.add(canonical_dihedral(s))
    regular_capacity={5:1,6:2,7:3,8:4}[k]
    exceptional_run_length=regular_capacity+1
    kept=[];pruned=[]
    for rep in sorted(seen):
        r=inner_runs(list(rep))
        violates=max(r)>exceptional_run_length or r.count(exceptional_run_length)>1
        (pruned if violates else kept).append(rep)
    assert len(kept)+len(pruned)==len(seen)
    remaining[k]=kept
    all_eliminated += [(k, ''.join(map(str,rep))) for rep in pruned]
    results.append(dict(inner=k,outer=15-k,total=len(seen),excluded=len(pruned),unknown=len(kept)))
assert [x['total'] for x in results]==[111,185,232,232]
assert sum(x['excluded'] for x in results)==117
assert sum(x['unknown'] for x in results)==643

out={"method":"exhaustive 15-bit dihedral orbit enumeration + exact-rational angular bounds",
     "status":"117 orbit classes ruled out, 643 remain UNKNOWN",
     "rational_bounds": {"B":str(B),"L_upper":str(LUB),"theta_lower":str(THETA_LO),
       "gamma_lower":str(GAMMA_LO),"alpha_5_3_lower":str(ALPHA_LO),
       "cap_angle_upper":{str(m):str(cap_ub(m)) for m in (7,8,9,10)}},
     "summary":results,"eliminated_representatives":all_eliminated,
     "unknown_representatives": {str(k):[''.join(map(str,x)) for x in v] for k,v in remaining.items()}}
with open('gap_pruning_certificate.json','w',encoding='utf-8') as f:
    json.dump(out,f,ensure_ascii=False,indent=2)
print('EXACT RATIONAL ANGLE INEQUALITIES PASSED')
print('DIHEDRAL PATTERN COUNTS AND SOUND EXCLUSIONS:')
for r in results: print(f"inner={r['inner']},outer={r['outer']}: {r['excluded']} eliminated of {r['total']}, {r['unknown']} UNKNOWN")
print(f"TOTAL: {sum(x['excluded'] for x in results)} eliminated; {sum(x['unknown'] for x in results)} UNKNOWN")
