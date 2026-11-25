import numpy as np, itertools as it, random, scipy.optimize as so
from scipy.sparse import csr_matrix, vstack
random.seed(427)
for n in range(10,15):
 k=n//2; edges=list(it.combinations(range(n),2)); m=len(edges)
 masks=np.array([s for s in range(1,1<<n) if s.bit_count()<=k]); sizes=np.array([int(s).bit_count() for s in masks]); members=((masks[:,None]>>np.arange(n))&1).astype(float)
 cuts=np.array([members[:,u]!=members[:,v] for u,v in edges],dtype=float).T
 A=csr_matrix(np.block([[-cuts,members,np.zeros((len(masks),1))],[-cuts,np.zeros_like(members),sizes[:,None]]]))
 c=np.r_[np.zeros(m),np.ones(n),-k]; lookup={s:i for i,s in enumerate(masks)}
 integ=np.r_[np.ones(m),np.zeros(n+1)]; bounds=so.Bounds(np.zeros(m+n+1),np.r_[np.ones(m),np.full(n+1,np.inf)])
 # all covering sets contain last vertex, and have k-1 members
 samples=[int(s) for s in masks if s.bit_count()==k-1 and s>>(n-1)==1]
 for trial in range(150):
  if n==10 and trial==0:ss=[771,594,664,564]
  else:
   ss=[];union=0
   while union!=(1<<n)-1:
    a=random.choice(samples)
    if a&~union==0:continue
    ss.append(a);union|=a
  eq=A[[lookup[s] for s in ss],:]
  cons=so.LinearConstraint(vstack([A,eq,csr_matrix(c[None,:])]),np.r_[np.full(A.shape[0],-np.inf),np.zeros(len(ss)),-np.inf],np.r_[np.zeros(A.shape[0]+len(ss)),-1/100])
  res=so.milp(c,integrality=integ,bounds=bounds,constraints=cons,options={'time_limit':1.5,'mip_rel_gap':0.01})
  if res.x is not None and res.fun < -1e-6:
   print('FOUND',n,k,res.fun,'cover',ss,'edges',[e for e,w in zip(edges,res.x[:m]) if w>.5],'x',res.x[m:-1],'h',res.x[-1],flush=True);raise SystemExit
  if trial%10==0:print('trial',n,trial,res.status,flush=True)
