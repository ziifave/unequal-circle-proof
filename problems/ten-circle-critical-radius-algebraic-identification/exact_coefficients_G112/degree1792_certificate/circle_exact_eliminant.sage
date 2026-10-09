# Requires SageMath (not installed in the execution environment used for this session).
# This is a proposed exact characteristic-zero computation. NOT EXECUTED here.
# It is intentionally strict: failure in a polynomial identity aborts immediately.

from sage.all import *
from itertools import permutations

# Build the multiquadratic field K = Q(sqrt(2),sqrt(3),sqrt(5),sqrt(7)).
K = QQ
S = {}
for n in [2,3,5,7]:
    Z = PolynomialRing(K,'z')
    z = Z.gen()
    L = K.extension(z*z - n, 's'+str(n))
    S = {i:L(v) for i,v in S.items()}
    S[n]=L.gen()
    K=L
assert K.absolute_degree()==16

r = {2:S[2], 5:S[5], 6:S[2]*S[3],7:S[7],8:2*S[2],9:K(3),10:S[2]*S[5]}
Xring = PolynomialRing(K,'R')
R = Xring.gen()
FX=Xring.fraction_field()
Wring=PolynomialRing(FX,'w')
w=Wring.gen()

def nd(i,j):
    D=(R-r[i])*(R-r[j])
    N=D-2*r[i]*r[j]
    return FX(N),FX(D)

def g_2(C1,C2):
    N1,D1=C1;N2,D2=C2
    return Wring([D2^2*N1^2 + D1^2*N2^2 - D1^2*D2^2,
             -2*N1*D1*N2*D2, D1^2*D2^2])

def g_extend(P,C):
    # Equivalent to Res_u(P(u), D^2*u^2 - 2*N*D*w*u + D^2*w^2 + N^2-D^2)
    assert P.degree()==2
    c,b,a=P[0],P[1],P[2]
    N,D=C
    A=D^2
    B=-2*N*D*w
    C0=Wring([N^2-D^2,0,D^2])
    L=a*B-A*b
    T=a*C0-A*c
    return (c*L^2 - b*L*T + a*T^2)/a

C=[nd(i,j) for i,j in [(7,9),(9,2),(2,8),(8,6)]]
P2=g_2(C[0],C[1])
P3=g_extend(P2,C[2])
assert P3.degree()==4

# The final angular resultant can be taken in the polynomial variable u.
# Sage's resultant is exact; no decimal approximations are used.
Uring=PolynomialRing(Wring,'u')
u=Uring.gen()
N,D=C[3]
P3_u=Uring([P3[i] for i in range(5)])
Q_u=Uring([Wring([N^2-D^2,0,D^2]), -2*N*D*w, D^2])
P4=P3_u.resultant(Q_u)
assert P4.degree()==8

# Triangle (5,7,10) and the closure edge (6,10).
d=r[5]+r[7]; b=r[7]+r[10]; a=r[5]+r[10]
lam=(b^2+d^2-a^2)/(2*d^2)
kap=4*r[5]*r[7]*r[10]*(r[5]+r[7]+r[10])/d^4
t5=R-r[5];t6=R-r[6];t7=R-r[7]
N57,D57=nd(5,7)
q=t5*N57-t7*D57
J=D57^2-N57^2
Ap=(t6^2+t7^2+b^2-(r[6]+r[10])^2)*D57 - 2*t6*t7*D57*w \
   + 2*lam*q*(t7-t6*w)
W=1-w^2
Ep=Ap^2+4*t6^2*kap*q^2*W \
   -J*(4*kap*t5^2*(t6*w-t7)^2 + 4*t6^2*lam^2*t5^2*W)
T=Ap*q-2*J*lam*t5^2*(t6*w-t7)
H=Ep^2-16*kap*t6^2*W*T^2
assert H.degree()==4

print('Computing characteristic-zero resultant; may require substantial RAM/time...',flush=True)
F=P4.resultant(H)
assert F.denominator()==1, 'Unexpected remaining denominators; inspect scaling'
Fn=Xring(F.numerator())
print('Raw resultant degree:',Fn.degree(),flush=True)

Dextr=(R+r[10])^16
for i in (2,5,6,7,8,9): Dextr *= (R-r[i])^32
qpoly,rem=Fn.quo_rem(Dextr)
assert rem==0, 'Apparent factors mod p do not divide in characteristic zero!'
assert qpoly.degree()==112, 'The residual has a different characteristic-zero degree!'
G=qpoly.monic()
print('Characteristic-zero quotient degree:',G.degree(),flush=True)
print('Irreducibility over K (may be expensive):',G.is_irreducible(),flush=True)
G.save('/mnt/data/circle_degree112_exact_K.sobj')
with open('/mnt/data/circle_degree112_exact_K.txt','w') as output:
    output.write(str(G))
print('Saved exact K[R] polynomial.',flush=True)
