"""Exact rational branch-and-bound on two surviving noncanonical 5+10 order types.
No floating point is used to accept an exclusion.
Requires the previous coarse-grid certificate result_all4.tsv as input.
"""
import sys,time,json
from fractions import Fraction as F
from functools import lru_cache
from certify_six_nine import B, SCALE, TWOPI, coslo, cmax
@lru_cache(maxsize=200000)
def ang(A,Bb):
 M=cmax(A,Bb)
 if M is None:return None
 if M>=1:return 0
 if M<=-1:return 8700
 lo,hi=0,8790
 while lo<hi:
  mid=(lo+hi+1)//2
  if coslo(mid)>=M:lo=mid
  else:hi=mid-1
 assert coslo(lo)>=M
 return lo

def detect(box, emit=False):
 e=[]; n=15
 for i in range(14):e.append((i+1,i,0,'O'))
 for i in range(n):
  for j in range(i+1,n):
   x,y=box[i],box[j]
   q=ang(x,y)
   if q is None:
    return ('SUM',(i,j))
   e.append((j,i,-q,'L'));e.append((i,j,TWOPI-q,'U'))
 ds=[0]*n;p=[None]*n;new=-1
 for k in range(n):
  new=-1
  for a,b,c,kind in e:
   if ds[b]>ds[a]+c:
    ds[b]=ds[a]+c;p[b]=(a,b,c,kind);new=b
  if new<0:return ('OPEN',None)
 v=new
 for k in range(n):v=p[v][0]
 seq=[];curr=v
 while True:
  z=p[curr];seq.append(z);curr=z[0]
  if curr==v:break
  assert len(seq)<16
 s=sum(z[2] for z in seq)
 assert s<0
 # Serialize a forward traversal; the checker will independently reconstruct
 # each edge weight from the rational box and verify the negative sum.
 cycle=tuple((u,v,kind) for u,v,w,kind in reversed(seq))
 return ('CYCLE', cycle)

def run(pattern,assign,max_nodes=1000000):
 ip=[i for i,c in enumerate(pattern) if c=='1']; box=[B[11]]*15
 for p,t in zip(ip,map(int,assign)):box[p]=B[t]
 counts={'SUM':0,'CYCLE':0,'NODES':0,'MAXDEPTH':0};cycmin=0
 def visit(depth):
  counts['NODES']+=1
  if counts['NODES']>max_nodes:raise RuntimeError('node limit')
  typ,v=detect(tuple(box))
  if typ!='OPEN':
   counts[typ]+=1
   return
  widths=[(box[p][1]-box[p][0], -p, p) for p in ip]
  width,_,p=max(widths)
  if width==0:raise RuntimeError('Unresolved singleton box: '+repr(box))
  counts['MAXDEPTH']=max(counts['MAXDEPTH'],depth+1)
  lo,hi=box[p];mid=(lo+hi)/2
  box[p]=(lo,mid);visit(depth+1)
  box[p]=(mid,hi);visit(depth+1)
  box[p]=(lo,hi)
 visit(0)
 return counts

if __name__=='__main__':
 start=time.time()
 rows=[]
 for line in open('full_residuals.txt'):
  a=line.strip().split('\t')
  if len(a)<6 or a[0]!='UNKNOWN' or a[2] not in ['000100100010101','000100100100101']:continue
  rows.append(a)
 expected={
  '000100100010101':{'coarse_boxes':47,'nodes':1641,'maxdepth':16,'cycles':844,'sums':0},
  '000100100100101':{'coarse_boxes':38,'nodes':646,'maxdepth':10,'cycles':342,'sums':0},
 }
 assert len(rows)==len(expected) and {a[2] for a in rows}==set(expected),[a[2] for a in rows]
 results=[]
 for a in rows:
  mask=a[2];seq=[x for x in a[5].split(',') if x]
  assert int(a[3])==int(a[4])==len(seq)==expected[mask]['coarse_boxes'],(mask,a[3:])
  assert len(seq)==len(set(seq)) and all(len(x)==5 and x.isdigit() for x in seq),mask
  print('START',mask,'coarse survivors',len(seq),flush=True)
  stats={'mask':mask,'coarse_boxes':len(seq),'certified':0,'nodes':0,'maxdepth':0,'cycles':0,'sums':0}
  for j,assignment in enumerate(seq):
   ans=run(mask,assignment)
   stats['certified']+=1;stats['nodes']+=ans['NODES'];stats['maxdepth']=max(stats['maxdepth'],ans['MAXDEPTH']);stats['cycles']+=ans['CYCLE'];stats['sums']+=ans['SUM']
   if (j+1)%10==0:print('PROGRESS',mask,j+1,'/',len(seq), 'nodes',stats['nodes'],'elapsed',round(time.time()-start,1),flush=True)
  results.append(stats)
  assert {k:v for k,v in stats.items() if k in expected[mask]}==expected[mask],('noncanonical exact-tree count mismatch',stats,expected[mask])
  print('CERTIFIED',stats,flush=True)
 assert len(results)==2
 with open('exact_noncanonical_report.json','w') as f:json.dump(results,f,indent=2)
 print('ALL TWO NONCANONICAL ORBITS CERTIFIED CLOSED IN EXACT ARITHMETIC. Seconds:',round(time.time()-start,2),'Trig comparisons cached:',ang.cache_info(),flush=True)
