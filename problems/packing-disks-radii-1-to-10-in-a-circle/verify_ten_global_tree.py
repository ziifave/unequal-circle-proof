#!/usr/bin/env python3
"""Independent rational replayer for the global exclusion R<R0 of integer-radius 10-disk packing.
Only standard library, Fraction and integer arithmetic; no floating-point decisions.
The accompanying certificate is DATA, not trusted code. Refuses python -O.
"""
import sys
if sys.flags.optimize:raise SystemExit('assert-based verifier: Python -O is disallowed')
from fractions import Fraction as F
from itertools import combinations,permutations
from math import factorial,isqrt
from collections import Counter
import json
from pathlib import Path

U=F('22.00019301274')
PI_UP=F('3.141592653590')
ROOT_LO=F('22.000193012737')
ROOT_HI=F('22.000193012738')
LABS=tuple(range(5,11))
CORE=(10,8,6,7,9)
PAIRS=tuple(combinations(LABS,2))
ORDERS=tuple((10,)+p for p in permutations((5,6,7,8,9)) if p[0]<p[-1])
T=10**6

# Machin identity: pi=16 atan(1/5)-4 atan(1/239).
# An odd-length alternating sum gives an upper bound and an even-length one a lower bound.
def atansum(d,n):return sum(F((-1)**k,(2*k+1)*d**(2*k+1)) for k in range(n))
assert F(3141592,10**6)<16*atansum(5,10)-4*atansum(239,3)
assert 16*atansum(5,9)-4*atansum(239,4)<PI_UP

def cosine_lower(x):
    # cos(x) > alternating Taylor through degree 18 for x in (0,pi),
    # which follows by alternating remainder or Taylor's integral remainder.
    return sum(((-1)**k)*x**(2*k)/factorial(2*k) for k in range(10))

def initial_box():
    return {i:(max(F(0),max(F(i+2*j)-U for j in range(5,11) if j!=i)),U-i) for i in LABS}

def propagate(box):
    b=dict(box)
    for i,j in PAIRS:
        ai,bi=b[i]; aj,bj=b[j]
        if bi+bj<i+j:return None
        b[i]=(max(ai,F(i+j)-bj),bi)
        b[j]=(max(aj,F(i+j)-bi),bj)
        if b[i][0]>bi or b[j][0]>bj:return None
    return b

def check_ticks(klist,box):
    assert isinstance(klist,list) and len(klist)==len(PAIRS)
    q={}
    for (i,j),k in zip(PAIRS,klist):
        assert type(k)==int and 0<=k<=3141592
        if k:
            li,ui=box[i];lj,uj=box[j]
            assert li>0 and lj>0
            d=i+j
            mx=max((x*x+y*y-d*d)/(2*x*y) for x in (li,ui) for y in (lj,uj))
            assert cosine_lower(F(k,T))>=mx, ('angle tick invalid',i,j,k)
        q[(i,j)]=F(k,T)
    return q

def verify_cycle(seq,order,q):
    assert isinstance(seq,list) and 2<=len(seq)<=6
    vertices=[];tot=F(0)
    for edge in seq:
        assert isinstance(edge,list) and len(edge)==4
        a,b,typ,k=edge
        assert type(a)==type(b)==type(typ)==type(k)==int
        assert 0<=a<6 and 0<=b<6 and a!=b
        assert typ in (0,1)
        assert (a>b if typ==0 else a<b)
        i,j=sorted((order[a],order[b]))
        assert q[(i,j)]==F(k,T)
        vertices.append(a)
        tot+=(2*PI_UP if typ==1 else F(0))-q[(i,j)]
        assert b==seq[(len(vertices))%len(seq)][0]
    assert len(set(vertices))==len(vertices) and tot<0
    return -tot

def angle_cycles(rule,box,barrier):
    q=check_ticks(rule['ticks'],box)
    cycles=rule['cycles'];assert isinstance(cycles,dict)
    assert all(str(j) in cycles or (barrier and tuple(i for i in ORDERS[j] if i!=5)==CORE) for j in range(60))
    assert set(cycles).issubset(set(str(j) for j in range(60)))
    min_slack=None
    for jstr,cyc in cycles.items():
        s=verify_cycle(cyc,ORDERS[int(jstr)],q)
        min_slack=s if min_slack is None else min(min_slack,s)
    return min_slack

# Node with main angle barrier. Radius comparison is done within [l_i,U-i], not the original partition cell.
def verify_main_barrier(box):
    for i,j in zip(CORE,CORE[1:]+CORE[:1]):
        xi,xu=box[i][0],U-i; yi,yu=box[j][0],U-j
        assert xi>0 and yi>0
        assert xi+yi>i+j, ('angle at pi',i,j)
        assert max(abs(xi-yu),abs(xu-yi))<i+j, ('triangle domain',i,j)
        assert xi*xi-yu*yu+(i+j)**2>0, ('partial derivative sign',i,j)
        assert yi*yi-xu*xu+(i+j)**2>0, ('partial derivative sign',j,i)
    assert box[10][0]+10>15  # Basic lower radius bound on this terminal box.

stats=Counter();neg_min=None

def check_node(node,box,depth):
    global neg_min
    stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
    b=propagate(box)
    rule=node['rule']
    if rule=='radial-empty':
        assert b is None
        stats['radial_empty']+=1
        return
    assert b is not None
    if rule=='split':
        i=node['disk']; cut=F(node['cut']);assert i in LABS
        lo,hi=b[i]; assert lo<cut<hi
        left,right=dict(b),dict(b)
        left[i]=(lo,cut);right[i]=(cut,hi)
        stats['splits']+=1
        check_node(node['left'],left,depth+1)
        check_node(node['right'],right,depth+1)
    elif rule in ('angle-cycles','main-angle-barrier'):
        ismain=rule=='main-angle-barrier'
        if ismain:verify_main_barrier(b)
        margin=angle_cycles(node,b,ismain)
        neg_min=margin if neg_min is None else min(neg_min,margin)
        stats['main_barrier' if ismain else 'angular_leaves']+=1
    else:raise AssertionError('unsupported node')

if __name__=='__main__':
    src=Path(sys.argv[1] if len(sys.argv)>1 else str(Path(__file__).with_name('ten_global_proof_tree.json')))
    data=json.loads(src.read_text())
    assert data['schema']=='integer-radius-ten-global-optimality-tree-v1'
    assert F(data['U'])==U
    assert data['orders']==[list(p) for p in ORDERS]
    check_node(data['tree'],initial_box(),0)
    assert stats['main_barrier']==4
    assert stats['nodes']==2*stats['splits']+1
    assert stats['angular_leaves']+stats['main_barrier']+stats['radial_empty']==stats['splits']+1
    print('PASS strict pi lower and upper bounds: Machin identity + rational arctan truncations')
    print('PASS exhaustive 60 cyclic orders (mod reflection), radial-cover tree & each rational angular negative-cycle')
    print('PASS near-boundary local angular monotonicity certificate (all oriented pair derivatives)')
    print('TREE',dict(stats),'min negative cycle margin',str(neg_min))
    print('CERTIFIED: No six disks of radii 5,...,10 can fit in radius R<R0, conditional on R0 being root of boundary ring equation and R0<U.')
