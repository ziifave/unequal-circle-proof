#!/usr/bin/env python3
"""Rational-only interval certificate for an exact simultaneous A=B=2*pi solution.
The interpretation as the SAME R0 from a separate algebraic certificate is not included.
"""
from fractions import Fraction as F
from math import isqrt
from dataclasses import dataclass

DIGITS=32
N=42
S=10**DIGITS

@dataclass(frozen=True)
class I:
    lo:F; hi:F
    def __post_init__(self): assert self.lo<=self.hi
    @staticmethod
    def coerce(x):
        if isinstance(x,I):return x
        return I(F(x),F(x))
    def __add__(self,o):
        o=self.coerce(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-self.coerce(o)
    def __rsub__(self,o):return self.coerce(o)-self
    def __mul__(self,o):
        o=self.coerce(o); q=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return I(min(q),max(q))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=self.coerce(o);assert o.lo>0 or o.hi<0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return self.coerce(o)/self
    def square(self):
        if self.lo>=0: return I(self.lo*self.lo,self.hi*self.hi)
        if self.hi<=0: return I(self.hi*self.hi,self.lo*self.lo)
        return I(F(0),max(self.lo*self.lo,self.hi*self.hi))
    def sqrt(self):
        assert self.lo>=0
        def sqrt_lo(x):return F(isqrt((x.numerator*S*S)//x.denominator),S)
        return I(sqrt_lo(self.lo),sqrt_lo(self.hi)+F(1,S))

def atan_bounds(q):
    q=I.coerce(q);assert q.lo>=0 and q.hi<F(1,2),q
    # q in [0,0.5]: even number of alternating terms is a strict lower bound
    def polynomial(v,terms):
        v2=v*v; power=v;total=F(0)
        for j in range(terms):
            total+=(1 if j%2==0 else -1)*power/F(2*j+1)
            power*=v2
        return total
    return I(polynomial(q.lo,N),polynomial(q.hi,N+1))

r={i:I(F(i),F(i)).sqrt() for i in range(1,11)}
pi=(16*atan_bounds(F(1,5))-4*atan_bounds(F(1,239)))

def half_quarter_angle_from_tan_half(v):
    # angle=4*atan(v/(1+sqrt(1+v^2))), where v=tan(angle/2)>0
    q=v/(1+(1+v.square()).sqrt())
    return 4*atan_bounds(q)

def alpha(i,t,R):
    a=R-r[i];d=r[10]+r[i]
    # tan(alpha/2)^2 = (d^2-(a-t)^2)/((a+t)^2-d^2)
    numerator=d.square()-(a-t).square()
    denominator=(a+t).square()-d.square()
    assert numerator.lo>0 and denominator.lo>0,(i,numerator,denominator)
    v=(numerator/denominator).sqrt()
    return half_quarter_angle_from_tan_half(v)

def beta(i,j,R):
    ai=R-r[i];aj=R-r[j];k=r[i]*r[j]
    v=(k/(ai*aj-k)).sqrt()
    return half_quarter_angle_from_tan_half(v)

def eval_fh(t,R):
    common=sum([beta(i,j,R) for i,j in ((7,9),(9,2),(2,8),(8,6))],I(F(0),F(0)))
    Fv=alpha(5,t,R)+beta(5,7,R)-alpha(7,t,R)
    Hv=alpha(7,t,R)+common+alpha(6,t,R)-2*pi
    return Fv,Hv

def alpha_R(i,t,R):
    a=R-r[i];d=r[10]+r[i];b=a.square()-d.square(); z=t.square()
    h=4*a.square()*z-(z+b).square()
    assert h.lo>0
    return -(a.square()+d.square()-z)/(a*h.sqrt())

def alpha_t(i,t,R):
    a=R-r[i];d=r[10]+r[i];b=a.square()-d.square();z=t.square()
    h=4*a.square()*z-(z+b).square()
    assert h.lo>0
    return (b-z)/(t*h.sqrt())

def beta_R(i,j,R):
    ai=R-r[i];aj=R-r[j];k=r[i]*r[j]
    return -(1/ai+1/aj)*(k/(ai*aj-k)).sqrt()

def F_R(t,R):return alpha_R(5,t,R)+beta_R(5,7,R)-alpha_R(7,t,R)
def H_t(t,R):return alpha_t(7,t,R)+alpha_t(6,t,R)

def small_sign(desc,v,expected):
    check(desc,v,expected)

def fmt(q):return f'{float(q):+.10g}'
def check(desc,v,expected):
    assert (v.hi<0 if expected=='negative' else v.lo>0),(desc,fmt(v.lo),fmt(v.hi))
    print('PASS',desc,expected,'bounds',fmt(v.lo),fmt(v.hi))

def main():
    # Broad rational enclosure of numerical critical solution; no floats in test.
    rl=F('8.30346812210');rh=F('8.30346812212')
    tl=F('1.00371608606');th=F('1.00371608609')
    rv=I(rl,rh);tv=I(tl,th)
    # Evaluate at the midpoints and use the mean-value theorem.
    rm=I((rl+rh)/2,(rl+rh)/2)
    tm=I((tl+th)/2,(tl+th)/2)
    dr=I(rl-(rl+rh)/2,rh-(rl+rh)/2)
    dt=I(tl-(tl+th)/2,th-(tl+th)/2)
    dFR=F_R(tv,rv)
    dHt=H_t(tv,rv)
    print('derivative F_R enclosure:', fmt(dFR.lo),fmt(dFR.hi))
    print('derivative H_t enclosure:', fmt(dHt.lo),fmt(dHt.hi))
    for desc,t,R,comp,sign in [
        ('F(t_low,R_box)',I(tl,tl),rm,0,'negative'),
        ('F(t_high,R_box)',I(th,th),rm,0,'positive'),
        ('H(t_box,R_low)',tm,I(rl,rl),1,'positive'),
        ('H(t_box,R_high)',tm,I(rh,rh),1,'negative'),
    ]:
        base=eval_fh(t,R)[comp]
        enclosure=base+(dFR*dr if comp==0 else dHt*dt)
        check(desc,enclosure,sign)
    print('CERTIFIED: Poincare-Miranda => one exact (t*, R*) inside the rational rectangle.')
    print('NOTE: connecting R* to pre-existing root R0 requires separate proof.')
if __name__=='__main__':main()

def certify_root_below_global_upper():
    """Refine the root rectangle to prove Rcrit < the v27 tree cap U.

    Poincare-Miranda boundary signs are checked with exact Fraction interval
    arithmetic. The right edge is R=U and H is strictly negative there, so the
    simultaneous root cannot lie on that edge.
    """
    rl=F('8.3034681221114890')
    rh=F('8.3034681221114900')  # exact v27 upper cap U
    tl=F('1.0037160860750841')
    th=F('1.0037160860750846')
    rv=I(rl,rh);tv=I(tl,th)
    rm=I((rl+rh)/2,(rl+rh)/2)
    tm=I((tl+th)/2,(tl+th)/2)
    dr=I(rl-(rl+rh)/2,rh-(rl+rh)/2)
    dt=I(tl-(tl+th)/2,th-(tl+th)/2)
    dFR=F_R(tv,rv)
    dHt=H_t(tv,rv)
    checks=[
        ('F(t_low,R_box)',eval_fh(I(tl,tl),rm)[0]+dFR*dr,'negative'),
        ('F(t_high,R_box)',eval_fh(I(th,th),rm)[0]+dFR*dr,'positive'),
        ('H(t_box,R_low)',eval_fh(tm,I(rl,rl))[1]+dHt*dt,'positive'),
        ('H(t_box,U)',eval_fh(tm,I(rh,rh))[1]+dHt*dt,'negative'),
    ]
    for label,value,sign in checks:
        check(label,value,sign)
    assert dFR.hi<0 and dHt.hi<0
    A_t=alpha_t(5,tv,rv)+alpha_t(6,tv,rv)
    B_t=dHt
    F_t=alpha_t(5,tv,rv)-alpha_t(7,tv,rv)
    B_R=(alpha_R(7,tv,rv)
         +sum([beta_R(i,j,rv) for i,j in ((7,9),(9,2),(2,8),(8,6))],I(F(0),F(0)))
         +alpha_R(6,tv,rv))
    assert A_t.lo>0 and B_t.hi<0 and B_R.hi<0 and F_t.lo>0
    print('CERTIFIED: a simultaneous exact angle root exists in the refined box,')
    print('  8.3034681221114890 <= Rcrit < U = 8.3034681221114900.')
    print('  Strictness follows from H(t,U)<0 on the entire top edge.')
    print('CERTIFIED: the root is unique in this box by strict derivative signs.')
    return {'R_lo':rl,'R_hi':rh,'t_lo':tl,'t_hi':th,
            'F_R':dFR,'F_t':F_t,'H_R':B_R,'H_t':B_t}

# Geometric post-check: exact symbolic angular closure from F=H=0, and
# interval certification of all non-contact distances over the root rectangle.
def geometry_core_check():
    rr=I(F('8.30346812210'),F('8.30346812212'))
    tt=I(F('1.00371608606'),F('1.00371608609'))
    assert (rr-tt-r[10]).lo>0
    order=(10,5,7,9,2,8,6)
    edges={(10,5),(10,7),(10,6),(5,7),(7,9),(9,2),(2,8),(8,6)}
    edges={frozenset(e) for e in edges}
    def rotation_cos_sin(i,j):
        if i==10:
            a=tt; b=rr-r[j];d=r[10]+r[j]
        else:
            a=rr-r[i];b=rr-r[j];d=r[i]+r[j]
        co=(a.square()+b.square()-d.square())/(2*a*b)
        assert co.lo> -1 and co.hi<1,(i,j,co.lo,co.hi)
        si=(1-co.square()).sqrt()
        return co,si
    c,s=I(F(1),F(1)),I(F(0),F(0))
    pts={10:(tt,I(F(0),F(0)))}
    for u,v in zip(order,order[1:]):
        C,S=rotation_cos_sin(u,v)
        c,s=c*C-s*S,s*C+c*S
        radius=rr-r[v]
        pts[v]=(radius*c,radius*s)
    count=0
    for ii,u in enumerate(order):
        for v in order[ii+1:]:
            if frozenset((u,v)) in edges:continue
            x1,y1=pts[u];x2,y2=pts[v]
            slack2=(x1-x2).square()+(y1-y2).square()-(r[u]+r[v]).square()
            assert slack2.lo>0,(u,v,slack2.lo,slack2.hi)
            count+=1
    assert count==13
    print('CERTIFIED: 7-circle contact realization has all 13 non-edge pairs strictly separated.')

if __name__=='__main__':
    geometry_core_check()

def interval_sign_proof():
    """Proves A_t>0, B_t<0 at R_crit and A_R,B_R<0 for 7.9<=R<=R_crit.

    Assumes only existence of R_crit in the rational box already certified above.
    """
    Rcrit=I(F('8.30346812210'), F('8.30346812212'))
    Rall=I(F('7.9'), Rcrit.hi)
    T=I(F('0.8588'),F('1.1265'))
    Z=T.square()
    def abd(i,R):
        a=R-r[i];d=r[10]+r[i]; b=a.square()-d.square()
        return a,b,d
    bb={};dd={}
    for i in (5,6,7):
        _,bb[i],dd[i]=abd(i,Rcrit)
    assert (bb[5]-Z).lo>0
    assert (bb[6]-Z).lo>0
    assert (Z-bb[7]).lo>0
    # Factor Q as X^2-Y^2. Coarse rational bounds suffice uniformly over
    # the certified Rcrit enclosure and the full t interval.
    assert dd[6].lo>F('5.6') and dd[7].hi<F('5.9')
    assert bb[7].hi<F('-1.6')
    assert bb[6].lo>F('2.75') and bb[6].hi<F('2.8')
    assert Z.lo>F('0.73')
    X_lower=F('5.6')*(F('0.73')+F('1.6'))
    Y_upper=F('5.9')*(F('2.8')-F('0.73'))
    assert X_lower>Y_upper
    print('CERTIFIED: B_t<0 by Q=(X-Y)(X+Y), with exact rational bounds')
    print('  X >',X_lower,'>',Y_upper,'> Y.')
    print('CERTIFIED: A_t>0 and B_t<0 at R=Rcrit throughout t in [0.8588,1.1265].')
    for i in (5,6,7):
        a,b,d=abd(i,Rall)
        assert (a-d+T.lo).lo>0
        assert (T.lo-(a-d)).lo>0
        assert (a+d-T.hi).lo>0
        assert (a.square()+d.square()-Z).lo>0
    for i,j in ((5,7),(7,9),(9,2),(2,8),(8,6)):
        ai=Rall-r[i];aj=Rall-r[j]
        assert (ai*aj-r[i]*r[j]).lo>0
    # These domain checks make each alpha_R and beta_R strictly negative,
    # so the sums A_R and B_R are negative term by term.
    print('CERTIFIED: every alpha_R and beta_R term is negative on the full domain.')
    print('CERTIFIED: A_R<0 and B_R<0 for R in [7.9,Rcrit], t in [0.8588,1.1265].')

if __name__=='__main__':
    interval_sign_proof()

def full_ten_check():
    """Exact 10-disk upper-bound witness using fixed rational centers for 1,3,4."""
    R=I(F('8.30346812210'),F('8.30346812212'))
    t=I(F('1.00371608606'),F('1.00371608609'))
    order=(10,5,7,9,2,8,6)
    contacts={frozenset(e) for e in ((10,5),(10,7),(10,6),(5,7),(7,9),(9,2),(2,8),(8,6))}
    def trig(u,v):
        au=(t if u==10 else R-r[u]); av=R-r[v];d=r[u]+r[v]
        co=(au.square()+av.square()-d.square())/(2*au*av)
        assert co.lo>-1 and co.hi<1
        return co,(1-co.square()).sqrt()
    co,si=I(F(1),F(1)),I(F(0),F(0))
    pts={10:(t,I(F(0),F(0)))}
    for u,v in zip(order,order[1:]):
        c,s=trig(u,v)
        co,si=co*c-si*s,si*c+co*s
        a=R-r[v]
        pts[v]=(a*co,a*si)
    for i,xx,yy in ((1,'-3.9798','6.1148'),(3,'6.4777','0.8849'),(4,'5.5222','-2.7574')):
        pts[i]=(I(F(xx),F(xx)),I(F(yy),F(yy)))
    assert len(pts)==10
    contain_lows=[]
    for i in (1,3,4):
        x,y=pts[i]
        residual=((R-r[i]).square()-x.square()-y.square())
        assert residual.lo>0,('containment',i)
        contain_lows.append((i,residual.lo))
    assert (R-t-r[10]).lo>0
    strict_count=0
    slack_lows=[]
    for i in range(1,11):
        for j in range(i+1,11):
            if frozenset((i,j)) in contacts:continue
            x,y=pts[i];u,v=pts[j]
            slack2=(x-u).square()+(y-v).square()-(r[i]+r[j]).square()
            assert slack2.lo>0,(i,j,float(slack2.lo))
            slack_lows.append((i,j,slack2.lo))
            strict_count+=1
    assert strict_count==37
    print('CERTIFIED: 10-circle upper-bound witness; 37 non-contact pairs strictly separated, 3 rational inside centers strictly contained.')
    print('smallest strict squared-separation lower bound',min(slack_lows,key=lambda x:x[2])[0:2],fmt(min(z[2] for z in slack_lows)))
    print('smallest internal containment-square lower bound',min(contain_lows,key=lambda x:x[1])[0],fmt(min(z[1] for z in contain_lows)))

if __name__=='__main__':
    full_ten_check()
