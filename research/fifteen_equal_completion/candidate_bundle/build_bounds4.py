from fractions import Fraction as F
from functools import lru_cache
B=[(F(0),F(1,2)),(F(1,2),F(1)),(F(1),F(3,2)),(F(3,2),F(8,5)),(F(8,5),F(5,3)),(F(5,3),F(17,10)),(F(17,10),F(37,20)),(F(37,20),F(2)),(F(2),F(43,20)),(F(43,20),F(23,10)),(F(23,10),F(2385432,1000000)),(F(35213569647,10000000000),F(35213569648,10000000000))]
SCALE=2800
@lru_cache(None)
def coslo(q):
 x=F(q,SCALE);y=x*x;t=F(1);s=t
 for j in range(1,10):
  t=-t*y/F(2*j*(2*j-1));s+=t
 # Taylor's theorem gives |cos(x)-P_18(x)| <= x^19/19! on x >= 0.
 # Subtract the remainder bound: P_18 alone is not a lower bound here.
 return s-x**19/F(121645100408832000)

def cmax(x,y):
 if x[0]==0 or y[0]==0:
  p=x if x[0]==0 else y
  oth=y if x[0]==0 else x
  if oth[1]<=2 and oth[0]>0:
   a=p[1];b=oth[1]
   return (a*a+b*b-4)/(2*a*b)
  return F(1)
 return max((a*a+b*b-4)/(2*a*b) for a in x for b in y)

def calc(x,y):
 M=cmax(x,y)
 if M>=1:return 0
 if M<=-1:return 8700
 lo,hi=0,8790
 while lo<hi:
  md=(lo+hi+1)//2
  if coslo(md)>=M:lo=md
  else:hi=md-1
 return lo
Q=[[calc(x,y) for y in B] for x in B]
with open('Q4.txt','w') as f:
 for row in Q:f.write(' '.join(map(str,row))+'\n')
for row in Q:print(row)
for i in range(len(B)):
 for j in range(len(B)):
  if Q[i][j] and cmax(B[i],B[j])<1:assert coslo(Q[i][j])>=cmax(B[i],B[j])
print('Verified rational trigonometric bounds:',sum(q>0 for row in Q for q in row))
