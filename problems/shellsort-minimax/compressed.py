"""Reverse product-of-chains DP with explicit marked-key transport, using only Python."""
from array import array
from itertools import product
from math import prod
from pathlib import Path
import argparse
import re

def mixed_max(n, H):
    if n<2 or not H or H[-1]!=1 or H[0]>=n or any(a<=b for a,b in zip(H,H[1:])):
        raise ValueError("illegal gap table")
    h=H[0]
    chains=[list(range(r,n,h)) for r in range(h)]
    caps=[len(c) for c in chains]
    bases=[k+1 for k in caps]
    strides=[prod(bases[r+1:]) for r in range(h)]
    size=prod(bases)
    budgets=array("I",[0])*size
    def prefixes(c):
        out=[0]
        for i in c:out.append(out[-1]|(1<<i))
        return out
    leading=[prefixes(c) for c in chains]
    passes=[]
    for g in H[1:]:
        cols=[prefixes(range(r,n,g)) for r in range(g)]
        pred=[cols[i%g][i//g] for i in range(n)]
        passes.append((g,cols,pred))
    for offset,digits in enumerate(product(*(range(k,-1,-1) for k in caps))):
        if offset==0:continue
        ix=size-1-offset
        S=sum(col[d] for col,d in zip(leading,digits))
        cache=[]
        for g,cols,pred in passes:
            counts=[(S&col[-1]).bit_count() for col in cols]
            cache.append((g,pred,S,counts))
            S=sum(col[k] for col,k in zip(cols,counts))
        best=0
        for r,digit in enumerate(digits):
            if digit==caps[r]:continue
            x=chains[r][digit]
            c=budgets[ix+strides[r]]
            for g,pred,mask,counts in cache:
                earlier=(pred[x]&mask).bit_count()
                c+=x//g-earlier+int(earlier>0)
                residue=x%g
                x=residue+g*counts[residue]
            best=max(best,c)
        budgets[ix]=best
    return sum(k*(k-1)//2 for k in caps)+budgets[0],size

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--bounds",default="logs/larger-bounds.txt")
    args=ap.parse_args()
    lines=Path(args.bounds).read_text().splitlines()
    seen=0
    for line in lines:
        m=re.fullmatch(r"n=(\d+) gaps=([\d,]+) max=(\d+) witness=([\d,]+)",line)
        if m:
            n,U=int(m[1]),int(m[3]); H=list(map(int,m[2].split(",")))
            value,size=mixed_max(n,H)
            if U!=value: raise ValueError((n,H,U,value))
            print(f"independent reverse mixed-radix n={n} gaps={H} states={size} exact={value}",flush=True)
            seen+=1
    if not seen:raise ValueError("no input rows")
