"""High-precision numerical sanity check; not an exact proof."""
import csv
from fractions import Fraction
from pathlib import Path
import mpmath as mp
mp.mp.dps=1200
rs={i:mp.sqrt(i) for i in (2,5,6,7,8,9,10)}
r=lambda i:rs[i]
la=((r(7)+r(10))**2+(r(5)+r(7))**2-(r(5)+r(10))**2)/(2*(r(5)+r(7))**2)
mu=2*mp.sqrt(r(5)*r(7)*r(10)*(r(5)+r(7)+r(10)))/(r(5)+r(7))**2
def theta(R,i,j):return 2*mp.asin(mp.sqrt(r(i)*r(j)/((R-r(i))*(R-r(j)))))
def closure(R):
 p7=R-r(7)
 p5=(R-r(5))*mp.exp(1j*theta(R,5,7))
 p10=p7+(la+1j*mu)*(p5-p7)
 p6=(R-r(6))*mp.exp(-1j*sum(theta(R,i,j) for i,j in ((7,9),(9,2),(2,8),(8,6))))
 return abs(p6-p10)**2-(r(6)+r(10))**2
rho=mp.findroot(closure,(mp.mpf('8.30346812'),mp.mpf('8.30346813')))
print('rho',mp.nstr(rho,95))
rows=list(csv.DictReader(Path('/mnt/data/circle_G112_exact_coefficients.tsv').open(),delimiter='\t'))
primes=(2,3,5,7)
basis=[]
for mask in range(16):
 elem=mp.mpf(1)
 for j,n in enumerate(primes):
  if mask>>j&1:elem*=mp.sqrt(n)
 basis.append(elem)
coefs=[]
for row in rows:
    v=mp.mpf(0)
    for j in range(16):
      q=Fraction(row[f'basis_{j}'])
      v+=(mp.mpf(str(q.numerator))/mp.mpf(str(q.denominator)))*basis[j]
    coefs.append(v)
val=mp.mpf(0)
terms=mp.mpf(0)
for k in range(112,-1,-1):val=val*rho+coefs[k]
for k in range(113):terms+=abs(coefs[k])*rho**k
print('log10 absolute G(rho)',mp.nstr(mp.log10(abs(val)),10))
print('log10 relative residual',mp.nstr(mp.log10(abs(val)/terms),10))
print('log10 sum abs terms',mp.nstr(mp.log10(terms),10))
