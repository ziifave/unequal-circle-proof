"""Independent exact-rational proof of impossibility of both nine-disk cyclic orders.

No floating point calculation affects an acceptance decision. Candidate angle
bounds use math.acos only to choose integer ticks; exact rational Taylor lower
cosine bounds justify EVERY accepted angle bound.
"""
from fractions import Fraction as F
from math import isqrt, acos, floor
from functools import lru_cache
from collections import Counter
import json, sys, hashlib
from pathlib import Path

SCALE=10**12
ANGLE_SCALE=10**5
U=F('8.30346812212')
ORDERS=((10,3,7,5,8,4,6,9,2),(10,3,7,5,8,6,4,9,2))
ROOT_LO={i:F(isqrt(i*SCALE*SCALE), SCALE) for i in range(1,11)}
for i,r in ROOT_LO.items():
    assert r*r<=i and (r+F(1,SCALE))**2>i

# Machin identity π = 16 atan(1/5)-4 atan(1/239).
# For x>0 the alternating arctan series truncated at a positive term is
# an upper bound; at a negative term, a lower bound.
def atan_partial(den,terms):
    return sum(((-1)**k)*F(1,(2*k+1)*den**(2*k+1)) for k in range(terms))
PI_UP = 16*atan_partial(5,7)-4*atan_partial(239,2)
assert F(0)<PI_UP<F(355,113)
# 4 atan(1/5)-atan(1/239)=π/4: (5+i)^4(239-i)=114244(1+i)
assert (476*239+480)==(480*239-476)==114244

@lru_cache(maxsize=100000)
def cos_lower(q):
    # Taylor polynomial through degree 18 (negative final term).
    # The tail after that polynomial is positive for 0<=q<=355/113.
    assert 0<=q<F(355,113)
    term=F(1);out=term
    for k in range(1,10):
        term=term*(-q*q)/((2*k-1)*(2*k))
        out+=term
    return out

@lru_cache(maxsize=100000)
def angle_tick(c):
    """Find rational q=integer/100000 with provable q <= acos(c)."""
    if c>=1:return 0
    if c<=-1: return 0 # safe weakening (and never used for a valid full box)
    candidate=max(0,floor((acos(float(c))-0.00005)*ANGLE_SCALE))
    for v in range(candidate,-1,-1):
        q=F(v,ANGLE_SCALE)
        if cos_lower(q)>c:return v
    return 0

def setup(order):
    n=len(order)
    rad=[ROOT_LO[i] for i in order]
    widths=[U-r for r in rad]
    dist=[[rad[i]+rad[j] for j in range(n)] for i in range(n)]
    return widths,dist

def graph_status(box,dist,counts):
    # Ranges are (lower_i, upper_i), all exact rational endpoints.
    n=len(box); lo=[x[0] for x in box];hi=[x[1] for x in box]
    for i in range(n):
        lower=max([lo[i]]+[dist[i][j]-hi[j] for j in range(n) if i!=j])
        lo[i]=max(F(0),lower)
        if lo[i]>hi[i]:
            return 'RADIAL',None
    tightened=tuple(zip(lo,hi))
    d=[[None]*n for _ in range(n)]
    for i in range(n):d[i][i]=F(0)
    for i in range(n):
        for j in range(i+1,n):
            if hi[i]+hi[j]<dist[i][j]:return 'RADIAL',None
            if lo[i]<=0 or lo[j]<=0:
                qint=0
            else:
                values=[(x*x+y*y-dist[i][j]**2)/(2*x*y)
                        for x in (lo[i],hi[i]) for y in (lo[j],hi[j])]
                max_c=max(values)
                if max_c< -1:
                    # Such a box would already violate the radial-sum condition.
                    assert hi[i]+hi[j]<dist[i][j]
                    return 'RADIAL',None
                qint=angle_tick(max_c)
                if qint:
                    assert cos_lower(F(qint,ANGLE_SCALE))>max_c
            q=F(qint,ANGLE_SCALE)
            d[j][i]=-q
            d[i][j]=2*PI_UP-q
    for k in range(n):
        for i in range(n):
            if d[i][k] is None:continue
            for j in range(n):
                if d[k][j] is None:continue
                val=d[i][k]+d[k][j]
                if d[i][j] is None or val<d[i][j]:d[i][j]=val
        if any(d[i][i]<0 for i in range(n)):
            return 'ANGLE',None
    return 'SPLIT',tightened

def prove(order,record=True):
    upper,dist=setup(order)
    initial=tuple((F(0),x) for x in upper)
    stack=[(initial,0)]
    stats=Counter();records=[];maxdepth=0
    while stack:
        box,depth=stack.pop();stats['boxes']+=1;maxdepth=max(maxdepth,depth)
        status,b=graph_status(box,dist,stats)
        if status!='SPLIT':
            stats[status]+=1
            continue
        score=[(hi-lo)/(F(4,5)+F(3,5)*hi) for lo,hi in b]
        index=max(range(len(order)),key=lambda i:score[i])
        if score[index]<F(1,1000000):
            raise AssertionError(f'Undischarged tiny box, {order}, index {index}, {b}')
        pivot=sum(b[index])/2
        low=list(b);up=list(b)
        low[index]=(b[index][0],pivot)
        up[index]=(pivot,b[index][1])
        stack.append((tuple(up),depth+1))
        stack.append((tuple(low),depth+1))
        stats['split']+=1
        if len(records)<15:records.append((depth,order[index],str(pivot)))
        if stats['boxes']%1000==0:
            print('RUNNING',order,stats,flush=True)
        if stats['boxes']>500000:raise AssertionError('Exceeded safety budget')
    assert stats['ANGLE']+stats['RADIAL']==stats['split']+1
    result={'order':list(order),'boxes':stats['boxes'],'angle_closed':stats['ANGLE'],
            'radial_closed':stats['RADIAL'],'internal_nodes':stats['split'],
            'max_depth':maxdepth,'initial_upper':[str(q) for q in upper],
            'first_splits':records,'status':'PROVED_NO_PACKING_AT_U'}
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)
    return result

if __name__=='__main__':
    results=[prove(order) for order in ORDERS]
    data={'theorem':'No nonoverlapping nine circles of radii sqrt(i), i=2..10, in container radius U, with either specified cyclic order',
          'U':str(U),'sqrt_lower_scale':SCALE,'angle_scale':ANGLE_SCALE,
          'pi_upper':str(PI_UP),'cases':results}
    path=Path(__file__).with_name('alternative_nine_exact_proof.json')
    with open(path,'w') as f:json.dump(data,f,indent=2)
    print('EXACT CERTIFICATE SAVED',path, 'sha256',hashlib.sha256(open(path,'rb').read()).hexdigest())
