from fractions import Fraction as F
from functools import lru_cache
B=[(F(0),F(1,2)),(F(1,2),F(1)),(F(1),F(3,2)),(F(3,2),F(8,5)),(F(8,5),F(5,3)),(F(5,3),F(17,10)),(F(17,10),F(37,20)),(F(37,20),F(2)),(F(2),F(43,20)),(F(43,20),F(23,10)),(F(23,10),F(2385432,1000000)),(F(35213569647,10000000000),F(35213569648,10000000000))]
SCALE=2800; TWOPI=17600
@lru_cache(None)
def coslo(q):
 x=F(q,SCALE);y=x*x;t=F(1);s=t
 for j in range(1,10):
  t=-t*y/F(2*j*(2*j-1));s+=t
 # Taylor's theorem gives |cos(x)-P_18(x)| <= x^19/19! on x >= 0.
 # Subtract the remainder bound: P_18 alone is not a lower bound here.
 return s-x**19/F(121645100408832000)

def cmax(x,y):
 if x[1]+y[1]<2:return None
 if x[0]==0 or y[0]==0:
  p=x if x[0]==0 else y;oth=y if x[0]==0 else x
  if oth[1]<=2 and oth[0]>0:
   a=p[1];b=oth[1]
   return (a*a+b*b-4)/(2*a*b)
  return F(1)
 return max((a*a+b*b-4)/(2*a*b) for a in x for b in y)

def calc(x,y):
 M=cmax(x,y)
 if M is None:return None
 if M>=1:return 0
 if M<=-1:return 8700
 lo,hi=0,8790
 while lo<hi:
  md=(lo+hi+1)//2
  if coslo(md)>=M:lo=md
  else:hi=md-1
 assert coslo(lo)>=M
 return lo

def cycle(rad):
 E=[];n=len(rad)
 for i in range(n-1):E.append((i+1,i,0,'ORDER'))
 for i in range(n):
  for j in range(i+1,n):
   q=calc(rad[i],rad[j])
   if q is None:return {'reason':'PAIR_SUM', 'pair':(i,j),'max_sum':str(rad[i][1]+rad[j][1])}
   E.append((j,i,-q,'LOWER'));E.append((i,j,TWOPI-q,'UPPER'))
 d=[0]*n;pred=[None]*n;upd=None
 for k in range(n):
  upd=None
  for e in E:
   u,v,w,typ=e
   if d[v]>d[u]+w:
    d[v]=d[u]+w;pred[v]=e;upd=v
  if upd is None:break
 if upd is None:return {'reason':'UNKNOWN'}
 v=upd
 for k in range(n):v=pred[v][0]
 cur=v;ret=[]
 while True:
  e=pred[cur];ret.append(e);cur=e[0]
  if cur==v:break
  assert len(ret)<n+1
 ret.reverse();W=sum(e[2] for e in ret)
 assert W<0
 for e in ret:
  u,v,w,typ=e
  if typ=='ORDER':assert w==0
  elif typ=='LOWER':assert coslo(-w)>=cmax(rad[u],rad[v])
  elif typ=='UPPER':assert coslo(TWOPI-w)>=cmax(rad[u],rad[v])
 return {'reason':'NEGATIVE_CYCLE','weight_numerator':W,'length':len(ret),'edges':ret}

if __name__=='__main__':
 mask='001001001001011';ipos=[i for i,x in enumerate(mask) if x=='1']
 for a in ['636808','646808','656808']:
  for z in [0,1]:
   rad=[B[11]]*15
   for j,p in enumerate(ipos):
    t=int(a[j]);rad[p]=B[t]
    if t==0:rad[p]=(F(0),F(1,4)) if z==0 else (F(1,4),F(1,2))
   c=cycle(rad)
   print(a,'small half',z,'=>',c['reason'],'weight numerator',c.get('weight_numerator'),'cycle length',c.get('length'), 'pair', c.get('pair'))
   if c['reason']=='NEGATIVE_CYCLE':
    print('  edges:', [(u,v,w) for u,v,w,t in c['edges']])
   assert c['reason']!='UNKNOWN'
 print('ALL SIX SUBBOXES CLOSED BY EXACT FRACTIONS')
