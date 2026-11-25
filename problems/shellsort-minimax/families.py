"""Independent checks of the restricted-family mathematics and finite-size bounds."""
from itertools import combinations
from math import comb, isqrt
from pathlib import Path
import argparse
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from audit import B, I, gaps, nested, run, require

def optimum_two(n, candidates):
    scores=[(I(n,h)+B(n,h),h) for h in sorted(set(candidates))]
    v=min(t[0] for t in scores)
    return v,[h for score,h in scores if score==v]

def quotient_candidates(n):
    h=2
    while h<n:
        q=n//h
        end=min(n-1,n//q)
        if n%q==0 and n//q==end:
            yield end
            end-=1
        if h<=end:
            num=(4*n+1)*(q+1)-4
            den=2*(q+1)*(2*q+1)
            yield min(end,max(h,num//den))
            yield min(end,max(h,(num+den-1)//den))
        h=n//q+1

def extremal(n,h):
    rows=[list(range(r,n,h)) for r in range(h)]
    order=sorted(range(h),key=lambda r:(-len(rows[r]),-r))
    a=[0]*n
    k=0
    for r in order:
        for pos in reversed(rows[r]):
            a[pos]=k; k+=1
    return a

def check_restricted():
    for n in range(3,421):
        a=optimum_two(n,range(2,n))
        b=optimum_two(n,quotient_candidates(n))
        require(a==b,("two-pass ties",n,a,b))
        for h in range(2,n):
            q,r=divmod(n,h)
            W=I(n,h)+B(n,h)-n+(r or h)
            require(8*W==2*n*n+2*q*n+q*h*h+q*(2*r-h)**2+2*r*r+2*q*r-6*n+2*r,("identity",n,h))
            if n<=65 or h in a[1]:
                sorted_a,charges=run(extremal(n,h),[h,1])
                require(sum(map(sum,charges))==I(n,h)+B(n,h),("extremal",n,h))
    for exponent in range(1,15):
        n=2**exponent
        H=[2**j for j in range(1,exponent)]
        value=None
        wins=[]
        for k in range(len(H)+1):
            for chosen in combinations(reversed(H),k):
                sched=(*chosen,1)
                cost=nested(n,sched)
                if value is None or cost<value: value,wins=cost,[sched]
                elif cost==value:wins.append(sched)
        t,odd=divmod(exponent,2)
        ratios=([2] if odd else [])+[4]*t
        target=[]; g=n
        for ratio in ratios:g//=ratio;target.append(g)
        require(wins==[tuple(target)],("power-of-two ties",n,wins,target))
        scaled=3*n*(n-1)+(3*n*(5+7*t)-4*(5*n-4) if odd else 21*n*t-16*(n-1))
        require(12*value==scaled,("closed cost",n,value))
    from itertools import permutations
    costs=[tuple(map(sum,run(p,[3,2,1])[1])) for p in permutations(range(5))]
    require(tuple(map(max,zip(*costs)))==(2,4,6) and max(map(sum,costs))==11,"incompatible passes")
    print("two-pass full scan/all ties n=3..420; integer expansion at every h; extremal execution through 65 and at every optimizer")
    print("all power-of-two subsequences m=1..14; extremal cost, uniqueness and both closed forms passed")
    print("n=5 (3,2,1), all 120 inputs: stage maxima 2,4,6 and joint maximum 11")

def partial(n,binary):
    # A short low-first-gap schedule is affordable to maximize exactly in this range.
    H=[9,7,4,1]
    out=subprocess.check_output([binary,str(n),"exact",*map(str,H)],text=True).strip()
    import re
    m=re.fullmatch(r"n=(\d+) gaps=9,7,4,1 max=(\d+) witness=([\d,]+)",out)
    if m is None or int(m[1])!=n:raise ValueError(out)
    U=int(m[2]);p=list(map(int,m[3].split(",")))
    require(sorted(p)==list(range(n)) and sum(map(sum,run(p,H)[1]))==U,"candidate witness")
    # Baseline distribution: each optional gap independently adds n-g.
    hist=[1]
    for add in range(1,n-1):
        old=hist; hist=old+[0]*add
        for i,c in enumerate(old):hist[i+add]+=c
    lost=sum(c for i,c in enumerate(hist) if i+n-1>U)
    require(sum(hist)==1<<(n-2),"coverage")
    print(out)
    print(f"size={n} exact fixed-table upper={U}; strict baseline exclusions={lost}; still to classify={(1<<(n-2))-lost}; schedules={1<<(n-2)}",flush=True)

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--partial",nargs="+",type=int)
    ap.add_argument("--binary")
    args=ap.parse_args()
    if args.partial:
        for n in args.partial:partial(n,args.binary)
    else:check_restricted()
