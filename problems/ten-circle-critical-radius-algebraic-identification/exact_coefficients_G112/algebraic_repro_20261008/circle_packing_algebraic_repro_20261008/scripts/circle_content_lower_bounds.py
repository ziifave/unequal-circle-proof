from itertools import permutations
from scipy.optimize import linear_sum_assignment
I=999999

def add(a,b):
 c=[I]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]=min(c[i],v)
 for i,v in enumerate(b):c[i]=min(c[i],v)
 return c

def mul(a,b):
 c=[I]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=min(c[i+j],x+y)
 return c

def scale(a,s):return [v+s for v in a]

def result(A,B):
 n=len(A)-1;m=len(B)-1
 M=[]
 for i in range(m):M.append([None]*i+A+[None]*(m-1-i))
 for i in range(n):M.append([None]*i+B+[None]*(n-1-i))
 out=[I]*(n*m+1)
 for pi in permutations(range(n+m)):
  pr=[0]
  for j,k in enumerate(pi):
   q=M[j][k]
   if q is None:break
   pr=mul(pr,q)
  else:out=add(out,pr)
 return out

def tval(at,i):return int(at==i)
def radval(at,i):return 0 # All radii and sums of radii are nonzero in char zero

def val(at):
 t=lambda i:tval(at,i)
 def nd(i,j):
  D=t(i)+t(j); N=min(D,0)
  return N,D
 def angle_poly(A,B):
  N,D=A;M,E=B
  return [[min(2*E+2*N,2*D+2*M,2*D+2*E)], [N+D+M+E], [2*D+2*E]]
 def quadratic(C):
  N,D=C
  return [[min(2*N,2*D),I,2*D],[I,N+D],[2*D]]
 C=[nd(i,j) for i,j in [(7,9),(9,2),(2,8),(8,6)]]
 P2=angle_poly(C[0],C[1]);P3=result(P2,quadratic(C[2]));P4=result([[v] for v in P3],quadratic(C[3]))
 # C for 5-7
 N,D=nd(5,7)
 t5,t6,t7=t(5),t(6),t(7)
 q=min(t5+N,t7+D)
 J=min(2*D,2*N)
 # Ap = (t6²+t7²+b²-(r6+r10)²)*D57 -2t6t7D57 w+2lambda q (t7-t6 w)
 Ap=[min(2*t6,2*t7,0)+D,t6+t7+D]
 Ap=add(Ap,[q+t7,q+t6])
 W=[0,I,0]
 e1=mul(Ap,Ap)
 e2=scale(W,2*t6+2*q)
 dif=[t7,t6]
 e3=scale(mul(dif,dif),J+2*t5)
 e4=scale(W,J+2*t6+2*t5)
 Ep=add(add(e1,e2),add(e3,e4))
 T=add(scale(Ap,q),scale(dif,J+2*t5))
 H=add(mul(Ep,Ep),scale(mul(W,mul(T,T)),2*t6))
 return [min(P2[0][0],P2[1][0],P2[2][0]), min(P3), min(P4),min(H)],P4,H,None

if __name__=='__main__':
 for a in (2,5,6,7,8,9,'minus10'):
  contents,p4,h,_=val(a)
  print(a,'P2P3P4H contents',contents,'P4',p4,'H',h)
  # dividing P4 by val min and H by val min yields resultant factor degree eP*deg H + eH*deg P
  print('   guaranteed content-based factor',min(p4)*4 + min(h)*8)
  if a in (2,8,9):assert min(p4)>=8
  if a in (6,7):assert all(v>=k for k,v in enumerate(p4))
 print('P4 VALUATION CONDITIONS: PASS')
