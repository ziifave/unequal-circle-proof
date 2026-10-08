"""Generate a finite exact-cycle witness tree. Float acos is suggestion only;
 every accepted lower angle and negative-cycle witness is rationally checked."""
import json, hashlib
from pathlib import Path
from fractions import Fraction as F
from certify_alternative_nine import (
   U, ORDERS, ROOT_LO, PI_UP, ANGLE_SCALE, angle_tick, cos_lower, setup,graph_status
)

def tightened(box,dist):
    n=len(box);lo=[x[0] for x in box];hi=[x[1] for x in box]
    for i in range(n):
        lo[i]=max(F(0),lo[i],*(dist[i][j]-hi[j] for j in range(n) if i!=j))
    return tuple(zip(lo,hi))

def angles(box,dist):
    n=len(box); q={}
    for i in range(n):
        for j in range(i+1,n):
            li,ui=box[i];lj,uj=box[j]
            if li<=0 or lj<=0:q[i,j]=0;continue
            c=max((x*x+y*y-dist[i][j]**2)/(2*x*y)
                  for x in (li,ui) for y in (lj,uj))
            k=angle_tick(c)
            if k: assert cos_lower(F(k,ANGLE_SCALE))>c
            q[i,j]=k
    return q

def negative_cycle(box,dist):
    n=len(box);q=angles(box,dist)
    edges=[]
    for i in range(n):
        for j in range(i+1,n):
            theta=F(q[i,j],ANGLE_SCALE)
            edges.append((i,j,2*PI_UP-theta,q[i,j]))
            edges.append((j,i,-theta,q[i,j]))
    distv=[F(0)]*n;prev=[None]*n;final=None
    for _ in range(n):
        final=None
        for i,j,w,k in edges:
            if distv[j] > distv[i]+w:
                distv[j] = distv[i]+w
                prev[j]=(i,k)
                final=j
    assert final is not None, 'Floyd says infeasible but Bellman-Ford found no cycle'
    v=final
    for _ in range(n):v=prev[v][0]
    end=v;back=[]
    while True:
        i,k=prev[v]
        back.append((i,v,k))
        v=i
        if v==end:break
        assert len(back)<=n
    cyc=list(reversed(back))
    assert len(cyc)>=2 and cyc[-1][1]==cyc[0][0]
    cost=sum((2*PI_UP-F(k,ANGLE_SCALE)) if i<j else -F(k,ANGLE_SCALE) for i,j,k in cyc)
    assert cost<0
    return {'edges':[[i,j,k] for i,j,k in cyc]}

def make(order):
    upper,dist=setup(order)
    root={};stack=[(tuple((F(0),v) for v in upper),root)]
    nodes=leaves=0;max_depth=0
    while stack:
        box,node=stack.pop();nodes+=1
        stat,b=graph_status(box,dist,{})
        b=tightened(box,dist)
        if stat=='ANGLE':
            node.update(negative_cycle(b,dist))
            leaves+=1
        elif stat=='RADIAL':
            raise AssertionError('unexpected radial terminal')
        else:
            assert stat=='SPLIT'
            scores=[(hi-lo)/(F(4,5)+F(3,5)*hi) for lo,hi in b]
            index=max(range(len(order)),key=lambda i:scores[i]);pivot=sum(b[index])/2
            node['split_disk']=order[index]
            node['pivot']=str(pivot)
            node['left']={};node['right']={}
            lo_b=list(b);hi_b=list(b)
            lo_b[index]=(b[index][0],pivot)
            hi_b[index]=(pivot,b[index][1])
            stack.append((tuple(hi_b),node['right']))
            stack.append((tuple(lo_b),node['left']))
    print(f'ORDER {order} NODES {nodes} LEAVES {leaves}')
    return root

if __name__=='__main__':
    obj={'description':'Exact dyadic radial partition and rational angular negative cycles',
         'U':str(U),'orders':[{'order':list(order),'tree':make(order)} for order in ORDERS]}
    out=Path(__file__).with_name('nine_circle_cycle_certificate.json')
    with open(out,'w') as f:json.dump(obj,f,ensure_ascii=False,separators=(',',':'))
    print('SIZE',len(open(out,'rb').read()),'SHA256',hashlib.sha256(open(out,'rb').read()).hexdigest())
