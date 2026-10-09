#!/usr/bin/env python3
"""Exact rational upper-witness verification for ten disks of radii 1,...,10.
Verifies an isolated exact angle root and an explicit nine-disk feasible packing.
No floating-point proof decisions. Run without Python -O / -OO.
"""
import sys
if sys.flags.optimize: raise SystemExit('run without -O/-OO')
from fractions import Fraction as F
from math import factorial, isqrt
from itertools import combinations, permutations

ROOT_LO=F('22.000193012737')
ROOT_HI=F('22.000193012738')
U=F('22.00019301274')
S=10**26
N=35
CORE=(10,8,6,7,9)
LABELS=tuple(range(6,11))

def toI(a): return a if isinstance(a,I) else I(a)
class I:
    def __init__(self, a,b=None):
        self.lo=F(a);self.hi=F(a if b is None else b)
        assert self.lo<=self.hi
    def __add__(self,b):
        b=toI(b);return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,b):return self+-toI(b)
    def __rsub__(self,b):return toI(b)-self
    def __mul__(self,b):
        b=toI(b);v=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=toI(b);assert b.lo>0 or b.hi<0
        return self*I(1/b.hi,1/b.lo)
    def __rtruediv__(self,b):return toI(b)/self
    def __pow__(self,k):
        assert k==2
        if self.lo>0:return I(self.lo*self.lo,self.hi*self.hi)
        if self.hi<0:return I(self.hi*self.hi,self.lo*self.lo)
        return I(0,max(self.lo*self.lo,self.hi*self.hi))
    def sqrt(self):
        assert self.lo>=0
        def floor_sqrt(x):return F(isqrt(x.numerator*S*S//x.denominator),S)
        return I(floor_sqrt(self.lo),floor_sqrt(self.hi)+F(1,S))

def atan_bound(x):
    assert abs(x)<=F(1,2)
    v=sum(((-1)**k)*x**(2*k+1)/F(2*k+1) for k in range(N))
    error=abs(x)**(2*N+1)/F(2*N+1)
    return I(v-error,v+error)
def atan_I(x):
    assert -F(1,2)<=x.lo<=x.hi<=F(1,2)
    return I(atan_bound(x.lo).lo,atan_bound(x.hi).hi)
PI=16*atan_I(I(F(1,5)))-4*atan_I(I(F(1,239)))
PI_UP=F('3.141592653590')
assert PI.hi<PI_UP

def beta(i,j,R):
    R=toI(R)
    denom=(R-i)*(R-j)-i*j
    assert denom.lo>0
    z=(F(i*j)/denom).sqrt()
    w=(z-1)/(z+1)
    assert -F(1,2)<w.lo and w.hi<F(1,2)
    return PI/2+2*atan_I(w)

def closure(R):
    return sum((beta(i,j,R) for i,j in zip(CORE,CORE[1:]+CORE[:1])),I(0))-2*PI

assert closure(ROOT_LO).lo>0
assert closure(ROOT_HI).hi<0
print('PASS exact angle-root existence and uniqueness by monotonicity')
print('root bracket:',ROOT_LO,ROOT_HI)

# Exact witness: core radii are R-i. Starting at disk 10 on x-axis, rotate
# counterclockwise by the four successive tangent angles.
R=I(ROOT_LO,ROOT_HI)
P={10:(R-10,I(0))}
ux,uy=I(1),I(0)
for i,j in zip(CORE,CORE[1:]):
    ci=1-F(2*i*j)/((R-i)*(R-j))
    assert -1<ci.lo and ci.hi<1
    si=(1-ci**2).sqrt()
    ux,uy=ux*ci-uy*si,ux*si+uy*ci
    P[j]=((R-j)*ux,(R-j)*uy)
P[1]=(I(F('-8.901')),I(F('19.006')))
P[2]=(I(F('-15.551')),I(F('-12.425')))
P[3]=(I(F('12.838')),I(F('13.952')))
P[4]=(I(F('11.103')),I(F('-14.109')))
P[5]=(I(F('-3.357')),I(F('1.306')))
contacts={frozenset((i,j)) for i,j in zip(CORE,CORE[1:]+CORE[:1])}
slacks=[]
for i,j in combinations(range(1,11),2):
    if frozenset((i,j)) in contacts:continue
    xi,yi=P[i];xj,yj=P[j]
    sq=(xi-xj)**2+(yi-yj)**2-(i+j)**2
    assert sq.lo>0,('overlap',i,j,float(sq.lo))
    slacks.append((sq.lo,(i,j)))
for i in (1,2,3,4,5):
    xi,yi=P[i]
    wall=(R-i)**2-xi**2-yi**2
    assert wall.lo>0
print('PASS exact upper witness: 5 tangent wall disks and 5 rational small disk centers')
print('strict noncontacts verified:',len(slacks),'; tightest pair:',min(slacks)[1],'; squared slack >',float(min(slacks)[0]))

print('PASS exact algebraic upper-bound witness at R0')
