from pathlib import Path
"""Exact modular specialization of the R eliminant, valid modulo a split prime.
Use this to determine degree/factor patterns, NOT to claim rational minimal polynomial.
"""
import sympy as sp
from itertools import permutations
import random, time, sys

p = int(sys.argv[1]) if len(sys.argv)>1 else 1009
sqs = {}
for j in (2,3,5,7):
    x=sp.sqrt_mod(j,p)
    if x is None: raise ValueError(f'{j} not square modulo {p}')
    sqs[j]=int(x)

def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,v in enumerate(a):c[i]=v
    for i,v in enumerate(b):c[i]=(c[i]+v)%p
    return c

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        if v:
            for j,w in enumerate(b):
                c[i+j]=(c[i+j]+v*w)%p
    return c

def scale(a,v):return [x*v%p for x in a]

def minus(a,b):return add(a,scale(b,-1))

def det4(mat):
    # determinant polynomial matrix degree <=2, using Leibniz 24 terms
    out=[0]
    for perm in permutations(range(4)):
        inv=sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
        term=[1]
        for i,j in enumerate(perm):term=mul(term,mat[i][j])
        out=add(out,scale(term,-1 if inv%2 else 1))
    return out

def resultant(A,B):
    # small n,m evaluation in prime field
    A=list(A); B=list(B)
    while len(A)>1 and A[-1]==0:A.pop()
    while len(B)>1 and B[-1]==0:B.pop()
    n=len(A)-1;m=len(B)-1
    size=m+n
    M=[]
    for row in range(m):M.append([0]*row+A+[0]*(m-1-row))
    for row in range(n):M.append([0]*row+B+[0]*(n-1-row))
    det=1
    for col in range(size):
        ix=next((k for k in range(col,size) if M[k][col]),None)
        if ix is None:return 0
        if ix!=col:
            M[col],M[ix]=M[ix],M[col]
            det=(-det)%p
        pivot=M[col][col]
        det=det*pivot%p
        ipiv=pow(pivot,-1,p)
        for row in range(col+1,size):
            f=M[row][col]*ipiv%p
            if f:
                for j in range(col+1,size):M[row][j]=(M[row][j]-f*M[col][j])%p
                M[row][col]=0
    return det

def rad(i):
    v=1
    for j in (2,3,5,7):
        while i%j==0:
            v=v*sqs[j]%p
            i//=j
    assert i==1, i
    return v

R5,R7,R10=rad(5),rad(7),rad(10)
d=R5+R7; b=R7+R10; a=R5+R10
lam=(b*b+d*d-a*a)*pow(2*d*d,-1,p)%p
kap=4*R5*R7*R10*(R5+R7+R10)*pow(d,-4,p)%p

# Polynomial in w with constant coefficients mod p at each R.
def evaluate(R):
    rr={i:rad(i) for i in (2,5,6,7,8,9,10)}
    t={i:(R-rr[i])%p for i in rr}
    def ND(i,j):
        D=t[i]*t[j]%p
        N=(D-2*rr[i]*rr[j])%p
        return N,D
    c=[]
    for i,j in ((7,9),(9,2),(2,8),(8,6)):
        c.append(ND(i,j))
    def first_two(C1,C2):
        N1,D1=C1;N2,D2=C2
        return [ (D2*D2*N1*N1 + D1*D1*N2*N2 -D1*D1*D2*D2)%p,
                 (-2*N1*D1*N2*D2)%p, D1*D1*D2*D2%p ]
    def next_two(P,C):
        # degree2 monic-ish P=a*u²+b*u+c and Q=A*u²+B(w)*u+C(w)
        cc,bb,aa=P; N,D=C
        A=D*D%p; B=[0,-2*N*D%p]; CC=[(N*N-D*D)%p,0,D*D%p]
        L=minus(scale(B,aa),[A*bb%p]);K=minus(scale(CC,aa),[A*cc%p])
        numer=add(minus(scale(mul(L,L),cc),scale(mul(L,K),bb)),scale(mul(K,K),aa))
        inva=pow(aa,-1,p)
        return scale(numer,inva)
    P2=first_two(c[0],c[1])
    P3=next_two(P2,c[2])
    # P4=Res_u(P3(u),D^2*u²-2ND*w*u+D²*w² +N²-D²)
    a3=P3[-1]; i3=pow(a3,-1,p)
    Pmonic=[v*i3%p for v in P3]
    N,D=c[3]; AA=D*D%p
    # multiplication by u on Q[u]/Pmonic
    M=[[0]*4 for _ in range(4)]
    for j in range(3):M[j+1][j]=1
    for j in range(4):M[j][3]=-Pmonic[j]%p
    # u² multiplication
    M2=[[sum(M[i][k]*M[k][j] for k in range(4))%p for j in range(4)] for i in range(4)]
    Qmat=[]
    for i in range(4):
        row=[]
        for j in range(4):
            v0=(AA*M2[i][j] + (N*N-AA)*(i==j))%p
            v1=(-2*N*D*M[i][j])%p
            v2=(AA if i==j else 0)
            row.append([v0,v1,v2])
        Qmat.append(row)
    P4=scale(det4(Qmat),pow(a3,2,p))
    assert len(P4)==9
    # H numerator
    N57,D57=ND(5,7)
    Q=(t[5]*N57-t[7]*D57)%p
    J=(D57*D57-N57*N57)%p
    t5=t[5];t6=t[6];t7=t[7]
    B0=(t6*t6+t7*t7+b*b-(rr[6]+rr[10])**2)%p
    Ap=add(scale([B0, -2*t6*t7%p],D57),scale([t7,-t6%p],2*lam*Q%p))
    diff=[-t7,t6]
    W=[1,0,-1]
    Ep=add(mul(Ap,Ap),scale(W,4*t6*t6*kap*Q*Q%p))
    Ip=add(scale(mul(diff,diff),4*kap*t5*t5%p),scale(W,4*t6*t6*lam*lam*t5*t5%p))
    Ep=minus(Ep,scale(Ip,J))
    T=minus(scale(Ap,Q),scale(diff,2*J*lam*t5*t5%p))
    Hp=minus(mul(Ep,Ep),scale(mul(W,mul(T,T)),16*kap*t6*t6%p))
    while len(Hp)>1 and Hp[-1]==0: Hp.pop()
    if len(Hp)!=5: print("unexpected H degree", R, len(Hp)-1, "coeff", Hp); raise ZeroDivisionError()
    # generic degree may shrink modp if special x, skip only if 0 leading
    return resultant(P4,Hp)

if __name__=='__main__':
    print('prime',p,'sqs',sqs,'radii', {i:rad(i) for i in (2,5,6,7,8,9,10)},flush=True)
    # Evaluate at 400 points and interpolate in Newton form then to powers
    n=385
    st=time.time()
    xs=[];ys=[];i=0
    while len(xs)<n+8 and i<p:
        x=i;i+=1
        try: y=evaluate(x)
        except (ValueError, ZeroDivisionError): continue
        xs.append(x);ys.append(y)
        if len(xs)%40==0: print(len(xs), 'points',round(time.time()-st,1),'seconds',flush=True)
    # divided difference -> coefficients
    diffs=ys[:n]
    for j in range(1,n):
        for i in range(n-1,j-1,-1):
            diffs[i]=(diffs[i]-diffs[i-1])*pow(xs[i]-xs[i-j],-1,p)%p
    polys=[0]*n
    basis=[1]
    for i,ai in enumerate(diffs):
        for k,c0 in enumerate(basis):polys[k]=(polys[k]+ai*c0)%p
        if i+1<n: basis=mul(basis,[-xs[i],1])
    while polys and polys[-1]==0:polys.pop()
    print('Interpolated degree',len(polys)-1,'and time',time.time()-st,flush=True)
    for i in range(n,n+8):
        assert sum(polys[j]*pow(xs[i],j,p) for j in range(len(polys)))%p==ys[i], ('failed check at',xs[i])
    print('8 holdout evaluations OK', flush=True)
    X=sp.Symbol('X')
    pol=sp.Poly.from_list(list(reversed(polys)),X,modulus=p)
    print('factor start',time.time()-st,flush=True)
    _,fac=sp.factor_list(pol)
    print('factor degree multiplicity',[(f.degree(),k) for f,k in fac],flush=True)
    for f,k in fac:
        if f.degree()==1:
            print('linear root',(-f.all_coeffs()[1]*pow(int(f.all_coeffs()[0])%p,-1,p))%p, "multiplicity",k,flush=True)
    with open(str(Path(__file__).resolve().parents[1]/'data'/f'modular_eliminant_{p}.txt'),'w') as file:
        file.write('prime '+str(p)+'\n')
        file.write('sqrt residues '+str(sqs)+'\n')
        file.write('degree '+str(len(polys)-1)+'\n')
        file.write('factor degrees '+str([(f.degree(),k) for f,k in fac])+'\n')
        file.write('coefficients ascending '+str(polys)+'\n')
    print('Done',time.time()-st,flush=True)
