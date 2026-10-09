"""Exact rational exhaustive branch-and-bound for the canonical (I,O,O)^5 pattern.
Branches either prove a negative angular cycle, a pair-sum contradiction, or land in the
local region [42/25,43/25]^5, to be certified separately by a local angular barrier.
"""
import sys,time,json
from fractions import Fraction as F
from verify_noncanonical_exact import ang,detect
from certify_six_nine import B
LOCAL_LO=F(42,25);LOCAL_HI=F(43,25)
PATTERN='001001001001001'
IPOS=[i for i,c in enumerate(PATTERN) if c=='1']
def run(assign,max_nodes=1000000):
 box=[B[11]]*15
 for p,t in zip(IPOS,map(int,assign)):box[p]=B[t]
 counts={'SUM':0,'CYCLE':0,'LOCAL':0,'NODES':0,'MAXDEPTH':0}
 def visit(depth):
  counts['NODES']+=1
  if counts['NODES']>max_nodes:raise RuntimeError('node limit')
  if all(LOCAL_LO<=box[p][0] and box[p][1]<=LOCAL_HI for p in IPOS):
   counts['LOCAL']+=1
   return
  typ,_=detect(tuple(box))
  if typ!='OPEN':
   counts[typ]+=1
   return
  width,_,p=max((box[p][1]-box[p][0],-p,p) for p in IPOS)
  if width==0:raise RuntimeError('OPEN POINT'+str(box))
  lo,hi=box[p];mid=(lo+hi)/2
  counts['MAXDEPTH']=max(counts['MAXDEPTH'],depth+1)
  box[p]=(lo,mid);visit(depth+1)
  box[p]=(mid,hi);visit(depth+1)
  box[p]=(lo,hi)
 visit(0)
 return counts

if __name__=='__main__':
 t=time.time();data=None
 for line in open('full_residuals.txt'):
  a=line.strip().split('\t')
  if len(a)>=6 and a[0]=='UNKNOWN' and a[2]==PATTERN:data=a;break
 assert data is not None
 assignments=[x for x in data[5].split(',') if x]
 assert int(data[3])==int(data[4])==len(assignments)==1181,(data[3:])
 assert len(assignments)==len(set(assignments))
 assert all(len(x)==len(IPOS) and x.isdigit() for x in assignments)
 print('START',PATTERN,'coarse boxes',data[3],flush=True)
 results={'coarse_boxes':0,'nodes':0,'cycles':0,'sums':0,'locals':0,'maxdepth':0}
 for j,ass in enumerate(assignments):
  r=run(ass,max_nodes=1000000)
  results['coarse_boxes']+=1
  results['nodes']+=r['NODES'];results['cycles']+=r['CYCLE'];results['sums']+=r['SUM'];results['locals']+=r['LOCAL'];results['maxdepth']=max(results['maxdepth'],r['MAXDEPTH'])
  if (j+1)%200==0:print('PROGRESS',j+1,'nodes',results['nodes'],'local leaves',results['locals'],'elapsed',round(time.time()-t,2),flush=True)
 expected={'coarse_boxes':1181,'nodes':56573,'cycles':28846,'sums':0,'locals':31,'maxdepth':23}
 assert results==expected,('canonical exact-tree count mismatch',results,expected)
 print('COMPLETE',results,'elapsed',round(time.time()-t,2),'cache',ang.cache_info(),flush=True)
 with open('canonical_exact_report.json','w') as f:json.dump(results,f,indent=2)
