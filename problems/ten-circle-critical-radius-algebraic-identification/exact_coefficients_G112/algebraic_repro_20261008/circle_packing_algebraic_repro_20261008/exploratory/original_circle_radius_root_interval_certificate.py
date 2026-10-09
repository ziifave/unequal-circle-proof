"""Exact rational interval certificate for the real packing closure root.
All interval endpoints are Fractions. Square roots rounded OUTWARDS using isqrt.
No floating point arithmetic is used in validation.
This certifies a root of the real contact-closure equation, NOT the 112-degree
char-zero factorization / degree 1792 minimal polynomial.
"""
from fractions import Fraction as F
from math import isqrt
from decimal import Decimal, localcontext

PREC=105
POW=10**PREC

class I:
    def __init__(self, a, b=None):
        if isinstance(a, I):
            self.lo,self.hi=a.lo,a.hi
        else:
            self.lo=F(a)
            self.hi=F(a) if b is None else F(b)
            assert self.lo<=self.hi
    def __add__(self, o):
        o=I(o); return I(self.lo+o.lo, self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o); v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o); assert o.lo>0 or o.hi<0, 'divisor interval straddles zero'
        return self*I(F(1,o.hi),F(1,o.lo))
    def __rtruediv__(self,o):return I(o)/self
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        if n==0:return I(1)
        if n%2==0:
            a=abs(self.lo);b=abs(self.hi)
            lo=F(0) if self.lo<=0<=self.hi else min(a,b)**n
            hi=max(a,b)**n
            return I(lo,hi)
        z=I(1);q=self
        while n:
            if n&1:z=z*q
            q=q*q;n//=2
        return z
    def sqrt(self):
        assert self.lo>=0, 'negative sqrt interval'
        def lower(v):
            n=v.numerator*POW*POW//v.denominator
            return F(isqrt(n), POW)
        a=lower(self.lo);b=lower(self.hi)
        return I(a,b if b*b==self.hi else b+F(1,POW))
    def __repr__(self):return f'I({self.lo!s}, {self.hi!s})'

def asI(o):return I(o)

class D:
    def __init__(self, v, deriv=0):
        self.v=I(v);self.d=I(deriv)
    @staticmethod
    def asD(x):return x if isinstance(x,D) else D(x)
    def __add__(self,o):
        o=D.asD(o);return D(self.v+o.v,self.d+o.d)
    __radd__=__add__
    def __neg__(self):return D(-self.v,-self.d)
    def __sub__(self,o):return self+-D.asD(o)
    def __rsub__(self,o):return D.asD(o)+-self
    def __mul__(self,o):
        o=D.asD(o);return D(self.v*o.v,self.d*o.v+self.v*o.d)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=D.asD(o);return D(self.v/o.v,(self.d*o.v-self.v*o.d)/(o.v**2))
    def __rtruediv__(self,o):return D.asD(o)/self
    def __pow__(self,n):
        assert n>=0
        if n==0:return D(1)
        return D(self.v**n,n*self.v**(n-1)*self.d)
    def sqrt(self):
        root=self.v.sqrt()
        return D(root,self.d/(2*root))

def cmul(a,b):
    x,y=a;u,v=b
    return (x*u-y*v,x*v+y*u)

def closure(R):
    r={k:D(I(k).sqrt()) for k in [2,5,6,7,8,9,10]}
    def rad(k):return r[k]
    d=rad(5)+rad(7)
    a=rad(5)+rad(10)
    b=rad(7)+rad(10)
    lam=(b*b+d*d-a*a)/(2*d*d)
    mu=(4*rad(5)*rad(7)*rad(10)*(rad(5)+rad(7)+rad(10))/(d**4)).sqrt()
    t={k:R-rad(k) for k in r}
    def angle_cs(i,j):
        c=1-2*rad(i)*rad(j)/(t[i]*t[j])
        s=(1-c*c).sqrt()
        return c,s
    p7=(t[7],D(0))
    c57,s57=angle_cs(5,7)
    p5=(t[5]*c57,t[5]*s57)
    neg_sum=(D(1),D(0))
    for i,j in [(7,9),(9,2),(2,8),(8,6)]:
        c,s=angle_cs(i,j)
        neg_sum=cmul(neg_sum,(c,-s))
    p6=(t[6]*neg_sum[0],t[6]*neg_sum[1])
    z=(p5[0]-p7[0],p5[1]-p7[1])
    rot=cmul((lam,mu),z)
    p10=(p7[0]+rot[0],p7[1]+rot[1])
    dx=p6[0]-p10[0];dy=p6[1]-p10[1]
    return dx*dx+dy*dy-(rad(6)+rad(10))**2

def fmt(v, d=65):
    with localcontext() as ctx:
        ctx.prec=d+12
        return format(Decimal(v.numerator)/Decimal(v.denominator), f'.{min(d,48)}E')

def main():
    low='8.3034681221114890787043811875161993'
    high='8.3034681221114890787043811875161994'
    L=F(low);H=F(high)
    fl=closure(D(L));fh=closure(D(H))
    box=closure(D(I(L,H),I(1)))
    print('R_low =',low)
    print('R_high=',high)
    print('closure(low) bounds:',fmt(fl.v.lo), fmt(fl.v.hi))
    print('closure(high) bounds:',fmt(fh.v.lo), fmt(fh.v.hi))
    print('derivative on [low,high] bounds:',fmt(box.d.lo),fmt(box.d.hi))
    print('low strictly negative?',fl.v.hi<0)
    print('high strictly positive?',fh.v.lo>0)
    print('derivative strictly positive?',box.d.lo>0)
    assert fl.v.hi<0 and fh.v.lo>0 and box.d.lo>0
    print('CERTIFIED unique real zero of closure in given rational interval (assuming elementary construction).')
    # verify that the chain radicands were nonnegative via assertions above

if __name__=='__main__':main()
