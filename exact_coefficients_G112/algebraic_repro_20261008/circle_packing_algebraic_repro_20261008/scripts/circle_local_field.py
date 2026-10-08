"""Truncated exact arithmetic in Q(sqrt2,sqrt3,sqrt5,sqrt7)[h,w].
For testing local multiplicities of H at specified algebraic R.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
NUMS=(2,3,5,7)

class K:
 __slots__=('a',)
 def __init__(self,a=0):
  if isinstance(a,K): self.a=a.a
  elif isinstance(a,(int,F)):self.a=(F(a),)+(F(0),)*15
  else:self.a=tuple(F(x) for x in a)
 def __add__(x,y):
  y=K(y);return K(tuple(a+b for a,b in zip(x.a,y.a)))
 __radd__=__add__
 def __neg__(x):return K(tuple(-a for a in x.a))
 def __sub__(x,y):return x+-K(y)
 def __rsub__(x,y):return K(y)+-x
 def __mul__(x,y):
  if "P" in globals() and isinstance(y,P):return y*x
  y=K(y)
  c=[F(0)]*16
  for i,a in enumerate(x.a):
   if a==0:continue
   for j,b in enumerate(y.a):
    if b==0:continue
    m=i&j
    factor=1
    for k,n in enumerate(NUMS):
     if m>>k&1: factor*=n
    c[i^j]+=a*b*factor
  return K(c)
 __rmul__=__mul__
 def __truediv__(x,y):
  if not isinstance(y,(int,F)):raise TypeError('scalar denom only')
  return K(tuple(a/y for a in x.a))
 def __pow__(x,k):
  assert k>=0
  y=K(1)
  while k:
   if k&1:y=y*x
   x=x*x;k//=2
  return y
 def __eq__(x,y):return x.a==K(y).a
 def __bool__(x):return any(x.a)
 def __repr__(x):return str({i:str(a) for i,a in enumerate(x.a) if a})

rad={2:K([0,1]+[0]*14),3:K([0,0,1]+[0]*13),5:K([0]*4+[1]+[0]*11),7:K([0]*8+[1]+[0]*7)}
rad[6]=rad[2]*rad[3];rad[8]=2*rad[2];rad[9]=K(3);rad[10]=rad[2]*rad[5]

N=5
class P:
 __slots__=('v',)
 def __init__(x,obj=0):
  if isinstance(obj,P):x.v=obj.v
  elif isinstance(obj,list):x.v=tuple(K(z) for z in (obj[:N]+[0]*N)[:N])
  else:x.v=(K(obj),)+(K(0),)*(N-1)
 def __add__(x,y):
  y=P(y);return P([a+b for a,b in zip(x.v,y.v)])
 __radd__=__add__
 def __neg__(x):return P([-a for a in x.v])
 def __sub__(x,y):return x+-P(y)
 def __rsub__(x,y):return P(y)+-x
 def __mul__(x,y):
  y=P(y);c=[K(0) for i in range(N)]
  for i,a in enumerate(x.v):
   if not a:continue
   for j,b in enumerate(y.v[:N-i]):
    if b:c[i+j]=c[i+j]+a*b
  return P(c)
 __rmul__=__mul__
 def __pow__(x,k):
  assert k>=0
  y=P(1)
  while k:
   if k&1:y=y*x
   x=x*x;k//=2
  return y
 def __repr__(x):return str([(i,v) for i,v in enumerate(x.v) if v])

def wadd(A,B):
 C=[P(0) for j in range(max(len(A),len(B)))]
 for i,x in enumerate(A): C[i]=C[i]+x
 for i,x in enumerate(B): C[i]=C[i]+x
 return C

def wneg(A):return [-x for x in A]
def wsub(A,B):return wadd(A,wneg(B))
def wmul(A,B):
 C=[P(0) for j in range(len(A)+len(B)-1)]
 for i,x in enumerate(A):
  for j,y in enumerate(B): C[i+j]=C[i+j]+x*y
 return C

def wscale(A,c):return [x*P(c) for x in A]

def h_expansion(at):
 R=P(rad[at] if at!='minus10' else -rad[10])+P([0,1])
 ri={j:P(k) for j,k in rad.items()}
 t={i:R-r for i,r in ri.items()}
 r5,r7,r10=(rad[j] for j in (5,7,10))
 d=r5+r7; b=r7+r10; a=r5+r10
 dinv=(r7-r5)/2
 assert dinv*d == K(1)
 lam=(b*b+d*d-a*a)*(dinv**2)/2
 kap=4*r5*r7*r10*(r5+r7+r10)*(dinv**4)
 assert lam**2+kap==b*b*(dinv**2)
 D57=t[5]*t[7];N57=D57-2*ri[5]*ri[7]
 q=t[5]*N57-t[7]*D57
 J=D57**2-N57**2
 Ap=wadd(wscale([P(1)], (t[6]**2+t[7]**2+P(b*b)-(t[6]*0+ri[6]+ri[10])**2)*D57),wscale([P(0),P(1)],-2*t[6]*t[7]*D57))
 Ap=wadd(Ap, wscale([t[7],-t[6]],2*lam*q))
 W=[P(1),P(0),P(-1)]
 diff=[-t[7],t[6]]
 Ep=wadd(wmul(Ap,Ap),wscale(W,4*t[6]**2*kap*q**2))
 Ep=wsub(Ep,wscale(wadd(wscale(wmul(diff,diff),4*kap*t[5]**2),wscale(W,4*t[6]**2*lam**2*t[5]**2)),J))
 T=wsub(wscale(Ap,q),wscale(diff,2*J*lam*t[5]**2))
 H=wsub(wmul(Ep,Ep),wscale(wmul(W,wmul(T,T)),16*kap*t[6]**2))
 while len(H)<5:H.append(P(0))
 return H

if __name__=='__main__':
 for at in (5,6,7,'minus10'):
  H=h_expansion(at)
  vals=[next((i for i,a in enumerate(v.v) if a),N) for v in H]
  print('at',at,'H coefficient valuations ≥',vals,flush=True)
  if at==5: assert all(v>=4 for v in vals)
  elif at in (6,7): assert all(v>=k for k,v in enumerate(vals))
  elif at=='minus10': assert all(v>=2 for v in vals)
  print('EXACT VALUATION CONDITIONS: PASS',flush=True)
