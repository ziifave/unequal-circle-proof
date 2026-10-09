#!/usr/bin/env python3
"""Certificate DISCOVERY for integer-radius 9-disc packing; floating-point is only used in angle tick search. The independent verifier accepts integers/Fractions only."""
from fractions import Fraction as F
from itertools import permutations,combinations
from math import acos,pi,ceil,factorial
import json
import sys
U=F('19.23319390809'); labels=tuple(range(4,10)); edges_pairs=list(combinations(labels,2))
orders=tuple((9,)+p for p in permutations((4,5,6,7,8)) if p[0]<p[-1]); assert len(orders)==60
T=10**6

def make_initial():
    return {i:(max(F(0), max(F(i+2*j)-U for j in range(1,10) if j!=i)), U-i) for i in labels}

def propagate(box):
    a={k:box[k] for k in labels}
    for _ in range(3):
        for i,j in edges_pairs:
            if a[i][1]+a[j][1]<i+j:return None
            ai,bi=a[i];aj,bj=a[j]
            a[i]=(max(ai,F(i+j)-bj),bi)
            a[j]=(max(aj,F(i+j)-bi),bj)
            if a[i][0]>bi or a[j][0]>bj:return None
    return a

def cos_upper(i,j,b):
    x,y=b[i],b[j];d=i+j
    return max((xx*xx+yy*yy-d*d)/(2*xx*yy) for xx in x for yy in y)

def cos_lower(q):
    return sum((-1)**k*q**(2*k)/factorial(2*k) for k in range(10))

def ticks(box):
    ks={}
    for i,j in edges_pairs:
        cu=cos_upper(i,j,box)
        if cu>=1:kk=0
        else:kk=max(0,int((acos(max(-1,float(cu)))-0.000003)*T))
        if kk and cos_lower(F(kk,T))<=cu:
            # Carefully validated using exact rational Taylor; adjust if needed.
            while kk and cos_lower(F(kk,T))<=cu:kk-=1
        ks[(i,j)]=kk
    return ks

def cycle_for_order(order, ticks):
    # BF gives an exact negative-cycle witness. Signs are w.r.t a linear lifted angle order.
    E=[]
    for a,b in combinations(range(6),2):
        i,j=sorted((order[a],order[b]));k=ticks[(i,j)];q=F(k,T)
        E.append((b,a,-q,[b,a,0,k]))
        E.append((a,b,2*F('3.141592653590')-q,[a,b,1,k]))
    dist=[F(0)]*6; prev=[None]*6; last=None
    for _ in range(6):
        last=None
        for a,b,w,desc in E:
            if dist[a]+w<dist[b]:
                dist[b]=dist[a]+w;prev[b]=(a,desc);last=b
        if last is None:return None
    v=last
    for _ in range(6):v=prev[v][0]
    cyc=[]; start=v
    while True:
        u,e=prev[v];cyc.append(e);v=u
        if v==start:break
        assert len(cyc)<=6
    cyc.reverse()
    assert sum((F(2)*F('3.141592653590') if e[2] else F(0))-F(e[3],T) for e in cyc)<0
    return cyc

def terminal(box):
    # Extend each radial interval up to the actual wall radius R-i (<= U-i).
    for i,j in zip((9,5,7,6,8,4),(5,7,6,8,4,9)):
        xi,xu=box[i][0],U-i;yi,yu=box[j][0],U-j
        if xi+yi<=i+j:return False
        if max(abs(xi-yu),abs(xu-yi))>=i+j:return False
        if xi*xi-yu*yu+(i+j)**2<=0:return False
        if yi*yi-xu*xu+(i+j)**2<=0:return False
    return box[9][0]+9>17

n_nodes=0;n_closed=0;n_term=0;depthmax=0;rule_counts={}

def build(box, order_ids, depth=0):
    global n_nodes,n_closed,n_term,depthmax
    n_nodes+=1;depthmax=max(depthmax,depth)
    b=propagate(box)
    if b is None:n_closed+=1;return {'rule':'radial-empty'}
    q=ticks(b)
    survivors=[]; proof={}
    for k in order_ids:
        c=cycle_for_order(orders[k],q)
        if c is None:survivors.append(k)
        else:proof[str(k)]=c
    if not survivors:
        n_closed+=1
        return {'rule':'angle-cycles','ticks':[q[z] for z in edges_pairs], 'cycles':proof}
    if terminal(b) and survivors==[orders.index((9,4,8,6,7,5))]:
        n_term+=1
        return {'rule':'main-angle-barrier','ticks':[q[z] for z in edges_pairs], 'cycles':proof}
    # To keep checker small, only store cycle proof for leaves when all orders closed.
    # All orders originally unresolved must be checked again in every child.
    index=max(labels,key=lambda i:b[i][1]-b[i][0]); low,high=b[index];cut=(low+high)/2
    assert low<cut<high
    left,right=dict(b),dict(b)
    left[index]=(low,cut);right[index]=(cut,high)
    # no need to store intermediate angle constraints
    return {'rule':'split','disk':index,'cut':str(cut),'left':build(left,order_ids,depth+1),'right':build(right,order_ids,depth+1)}

if __name__=='__main__':
    tree=build(make_initial(),list(range(60)))
    obj={'schema':'integer-radius-nine-global-optimality-tree-v1','U':str(U),'orders':[list(p) for p in orders],'tree':tree}
    path=sys.argv[1] if len(sys.argv)>1 else '/mnt/data/nine_global_proof_tree.json'
    with open(path,'w') as f:json.dump(obj,f,separators=(',',':'))
    print('WROTE',path,'NODES',n_nodes,'CLOSED',n_closed,'MAIN_BARRIER',n_term,'MAX_DEPTH',depthmax)
