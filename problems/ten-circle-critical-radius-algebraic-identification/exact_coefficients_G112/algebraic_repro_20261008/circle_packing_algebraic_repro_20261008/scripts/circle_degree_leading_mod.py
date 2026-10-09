"""Finite field nonvanishing test for R^(-320)*eliminant(R) at infinity.
P4 limit after angular rescaling w=1-z/R^2; H similarly.
"""
from sympy import symbols,Poly, invert, resultant
p=10391
s={2:1360,3:2293,5:4804,7:4529}
def mul(x,y):return x*y%p
def sqrt(i):
 if i==2:return s[2]
 if i==5:return s[5]
 if i==6:return mul(s[2],s[3])
 if i==7:return s[7]
 if i==8:return 2*s[2]%p
 if i==9:return 3
 if i==10:return mul(s[2],s[5])
 raise ValueError(i)
r={i:sqrt(i) for i in (2,5,6,7,8,9,10)}
a={f'{i}{j}':2*r[i]*r[j]%p for i,j in [(7,9),(9,2),(2,8),(8,6)]}
z,u=symbols('z u')

def G(v,w,b):return (v-w-b)**2-4*w*b

a79,a92,a28,a86=(a[k] for k in ('79','92','28','86'))
# Two-contact normalized resultant for cosine cumulative-angle variable.
P2=Poly((u-a79-a92)**2-4*a79*a92,u,modulus=p)
P3=Poly(resultant(P2.as_expr(),G(z,u,a28),u),z,modulus=p)
P4=Poly(resultant(P3.as_expr().subs(z,u),G(z,u,a86),u),z,modulus=p)
# H8(z) = lim_{R->infty} R^-8 H(R,1-z/R²).
r5,r6,r7,r10=[r[i] for i in (5,6,7,10)]
d=(r5+r7)%p;b=(r7+r10)%p;aa=(r5+r10)%p
lam=(b*b+d*d-aa*aa)*invert(2*d*d,p)%p
kap=4*r5*r7*r10*(r5+r7+r10)*invert(d**4,p)%p
q=(r7-r5)%p;c=(r7-r6)%p;j=4*r5*r7%p
A=c*c+2*z+b*b-(r6+r10)**2+2*lam*q*(-c)
E=A**2+8*kap*q*q*z-4*j*(kap*c*c+2*lam*lam*z)
T=A*q-2*j*lam*c
H=Poly(E**2-32*kap*z*T**2,z,modulus=p)
lead=P4.resultant(H)
print('modulus',p)
print('P4limit degree',P4.degree(),'Hlimit degree',H.degree())
print('resultant of leading polynomials nonzero?',lead != 0)
print('leading resultant mod p',int(lead)%p)
assert lead!=0
