"""Standalone certificate replay: uses ONLY exact integers and Fraction arithmetic.
No trigonometric functions, floating-point arithmetic, optimization, or external
packages. All proof decisions are computed afresh from a finite JSON witness.
"""
from fractions import Fraction
from math import isqrt, factorial
from pathlib import Path
import json, hashlib

F=Fraction
U=F('8.30346812212')
S=10**12
T=10**5
ORDERS=((10,3,7,5,8,4,6,9,2),(10,3,7,5,8,6,4,9,2))

def atan_n(x,n):
    return sum(((-1)**k)*F(1,(2*k+1)*x**(2*k+1)) for k in range(n))

# Pure-rational proof of pi < pi_upper: Machin's arctangent identity
# (5+i)^4*(239-i)=114244*(1+i), with the argument π/4,
# so 16atan(1/5)-4atan(1/239)=π.
assert (476*239+480)==(480*239-476)==114244
PI_UP=16*atan_n(5,7)-4*atan_n(239,2)
assert F(3)<PI_UP<F(355,113)

rootlo={i:F(isqrt(i*S*S),S) for i in range(1,11)}
for i,r in rootlo.items():
    assert r*r<=i and (r+F(1,S))**2>i

def cos_lower(q):
    # Exact degree-18 Taylor lower polynomial. The next term is positive,
    # and its alternating-series tail is positive for 0<=q<355/113.
    assert 0<=q<F(355,113)
    return sum(((-1)**k)*q**(2*k)/factorial(2*k) for k in range(10))

def exact_proof(order,tree):
    n=len(order)
    initial=tuple((F(0),U-rootlo[i]) for i in order)
    d=[[rootlo[order[i]]+rootlo[order[j]] for j in range(n)] for i in range(n)]
    boxes=[(tree,initial,0)]
    closed=branches=0;max_depth=0;minimum_margin=None
    while boxes:
        node,box,depth=boxes.pop()
        max_depth=max(max_depth,depth)
        lo=[x[0] for x in box];hi=[x[1] for x in box]
        # Every feasible packing satisfies s_i+s_j>=r_i+r_j.
        for i in range(n):
            lo[i]=max(F(0),lo[i],*(d[i][j]-hi[j] for j in range(n) if j!=i))
            if lo[i]>hi[i]:
                raise AssertionError('Branch cannot be split; expected explicit radial witness')
        bounds=list(zip(lo,hi))
        if 'edges' in node:
            assert 'split_disk' not in node
            edges=node['edges'];assert 2<=len(edges)<=n
            weight=F(0)
            for ind,(i,j,k) in enumerate(edges):
                assert 0<=i<n and 0<=j<n and i!=j
                assert j==edges[(ind+1)%len(edges)][0]
                assert isinstance(k,int) and 0<=k<=314159
                a,b=sorted((i,j))
                q=F(k,T)
                if k:
                    ai,bi=bounds[a];aj,bj=bounds[b]
                    assert ai>0 and aj>0
                    # For x,y>0, c(x,y)=(x²+y²-d²)/(2xy)
                    # has NO interior maximum in either coordinate.
                    # Thus max c over the rectangle is attained at a corner.
                    mc=max((x*x+y*y-d[a][b]**2)/(2*x*y)
                           for x in (ai,bi) for y in (aj,bj))
                    assert cos_lower(q)>mc, ('angle witness invalid',order,depth,i,j,k)
                weight+=2*PI_UP-q if i<j else -q
            assert weight<0,('negative cycle not negative',order,depth)
            if minimum_margin is None or -weight<minimum_margin:minimum_margin=-weight
            closed+=1
        else:
            assert 'left' in node and 'right' in node
            idx=order.index(node['split_disk'])
            v=F(node['pivot'])
            assert lo[idx]<v<hi[idx]
            a=list(bounds);b=list(bounds)
            a[idx]=(lo[idx],v);b[idx]=(v,hi[idx])
            boxes.append((node['left'],tuple(a),depth+1))
            boxes.append((node['right'],tuple(b),depth+1))
            branches+=1
    assert closed==branches+1
    return dict(order=list(order),total_nodes=closed+branches,
                proved_leaves=closed,branch_nodes=branches,max_depth=max_depth,
                minimum_cycle_margin_radians=str(minimum_margin))

def main():
    path=Path(__file__).with_name('nine_circle_cycle_certificate.json')
    doc=json.loads(path.read_text())
    assert F(doc['U'])==U
    assert len(doc['orders'])==2
    results=[]
    for record,order in zip(doc['orders'],ORDERS):
        assert tuple(record['order'])==order
        res=exact_proof(order,record['tree'])
        print('PASS',res)
        results.append(res)
    print('CERTIFIED: both nine-disk cyclic orders impossible at R <=',U)
    print('CERTIFICATE SHA256:',hashlib.sha256(path.read_bytes()).hexdigest())

if __name__=='__main__':main()
