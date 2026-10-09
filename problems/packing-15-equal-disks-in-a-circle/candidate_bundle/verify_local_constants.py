"""Pure-integer/rational verification of local-barrier derivative constants.
Analytic steps explaining these constants are in LOCAL_BARRIER_PROOF.md.
"""
from fractions import Fraction as F
from math import isqrt
Z=F
T=10**26
def sqrtrange(q):
 assert q>0
 n=isqrt((q.numerator*T*T)//q.denominator)
 assert F(n*n,T*T)<=q<F((n+1)*(n+1),T*T)
 return F(n,T),F(n+1,T)
root5lo,root5hi=sqrtrange(F(5))
cotlo,cot_hi0=sqrtrange(1+2/root5hi)[0],sqrtrange(1+2/root5lo)[1]
blo=sqrtrange(1+(2+cotlo)**2)[0]
bhi=sqrtrange(1+(2+cot_hi0)**2)[1]
a0lo=sqrtrange(8/(5-root5lo))[0]
a0hi=sqrtrange(8/(5-root5hi))[1]
assert F(35213569647,10**10)<blo<bhi<F(35213569648,10**10)
assert F(1701,1000)<a0lo<a0hi<F(1702,1000)
assert F(4,5)<(1+root5lo)/4<(1+root5hi)/4<F(81,100)
lo,hi=F(42,25),F(43,25)
ylo,yhi=F(3521,1000),F(1761,500)
assert ylo<blo<bhi<yhi

def c(x,y):return (x*x+y*y-4)/(2*x*y)
assert c(lo,yhi)<F(95,100)
assert c(lo,lo)>0
assert max(c(a,b) for a in [lo,hi] for b in [lo,hi])<F(35,100)
# derivative bounds for c_h(x,y), x,y in [1.68,1.72]
chx=(hi*hi-lo*lo+4)/(2*lo*lo*lo)
chxx=(4-lo*lo)/(lo**4)
chxy=1/(lo*lo)+2/(lo**4)
assert chx<F(48,100)
assert chxx<F(15,100)
assert chxy<F(61,100)
# derivative bounds for c_k(x,b0), x in [1.68,1.72]
ckx=(yhi*yhi-lo*lo-4)/(2*lo*lo*ylo)
ckxx=(yhi*yhi-4)/(lo**3*ylo)
assert ckx<F(29,100)
assert ckxx<F(51,100)
# lower sin bound, hence 2nd derivative bounds
assert (F(35,100)**2+F(93,100)**2)<1
assert (F(95,100)**2+F(31,100)**2)<1
hesshxx=F(15,100)/F(93,100)+F(35,100)*F(48,100)**2/F(93,100)**3
hesshxy=F(61,100)/F(93,100)+F(35,100)*F(48,100)**2/F(93,100)**3
hesskxx=F(51,100)/F(31,100)+F(95,100)*F(29,100)**2/F(31,100)**3
assert hesshxx<F(3,10),hesshxx
assert hesshxy<F(8,10),hesshxy
assert hesskxx<F(5),hesskxx
# c=-h_x and d=k_x at symmetric radius
coslo=(1+root5lo)/4;coshi=(1+root5hi)/4
assert (1-coshi*coshi)/coshi>F(21,50)
assert (1-coslo*coslo)/coslo<F(1,2)<coslo
assert c(hi,ylo)>F(93,100)
min_kder=(ylo*ylo-hi*hi-4)/(2*hi*hi*yhi)
assert min_kder>F(26,100)
assert F(93,100)**2+F(37,100)**2>1
# At the base point, k_x = (-c_x)/sin(phi(x,b0)) > .26/.37 > .5 > c.
assert F(26,100)/F(37,100)>F(1,2)
local_coefficient_floor = F(2,5)*F(21,50)-F(5)*F(11,500)
assert local_coefficient_floor == F(29,500)
print('EXACT LOCAL COEFFICIENT CHECK PASSED (> 29/500 lower-bound coefficient)')
print('b0:',str(float(blo)),str(float(bhi)))
print('a0:',str(float(a0lo)),str(float(a0hi)))
print('Hxx(h)<0.3, Hxy(h)<0.8, Hxx(g)<5; local expansion coefficient positive')
