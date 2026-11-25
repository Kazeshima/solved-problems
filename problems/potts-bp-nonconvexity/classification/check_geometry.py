"""Deterministic falsification checks. Requires NumPy and SciPy; run as a script."""
from fractions import Fraction as Q
from itertools import product
import gzip
import json
from pathlib import Path
import platform
import numpy as np
import scipy
from scipy.optimize import brentq, least_squares
from scipy.spatial import ConvexHull


def counts(q, d):
    if q == 1:
        yield (d,)
    else:
        for k in range(d + 1):
            for tail in counts(q - 1, d - k):
                yield (k,) + tail


def rational_face(q, d, beta, samples):
    base = (d-2, 0, 0)
    zeros, checked = set(), 0
    for n in counts(q, d):
        v = [beta**k for k in n]
        slack = sum(v[i] / beta**base[i] for i in range(3)) - (1+2*beta)*sum(v[3:])/(q-3)
        samples.append(["signature",q,d,str(beta),n,str(slack)])
        assert slack >= 0
        if slack == 0:
            zeros.add(n)
        checked += 1
    expected = {tuple((base[i] + (i != k)) if i < 3 else 0 for i in range(q)) for k in range(3)}
    assert zeros == expected
    verts = [[beta**k for k in n] for n in sorted(zeros)]
    target = [sum(row[i] for row in verts) / sum(map(sum,verts)) for i in range(q)]
    assert sum(target) == 1 and all(v > 0 for v in target)
    S = 1/target[-1]
    assert all((1+base[i]*(1-beta)-S*target[i]/beta**base[i])/(1-beta) == base[i]+Q(2,3) for i in range(3))
    return {"q":q,"d":d,"beta":str(beta),"tested":checked,"equality_signatures":sorted(zeros),
            "target":[str(x) for x in target]}


def bp(p, beta):
    g=np.prod(1-(1-beta)*p,axis=0)
    return g/g.sum()


def exact_polygon(signatures, beta):
    points=[]
    for i,n in enumerate(signatures):
        v=[beta**int(k) for k in n]; z=sum(v)
        points.append((v[0]/z,v[1]/z,i))
    points.sort()
    def side(seq):
        a=[]
        for p in seq:
            while len(a)>=2:
                x,y=a[-2],a[-1]
                if (y[0]-x[0])*(p[1]-x[1])-(y[1]-x[1])*(p[0]-x[0])>0: break
                a.pop()
            a.append(p)
        return a[:-1]
    return [p[2] for p in side(points)+side(reversed(points))]


def zero_lift(x, d):
    q=len(x); k=int(np.argmax(x)); y=x/x[k]
    active=[i for i in range(q) if i!=k]
    r=brentq(lambda u:np.prod(1-u*y[active])-u,0,1,xtol=1e-15)
    p=np.full((d,q),1/q)
    for j,i in enumerate(active):
        p[j]=0
        p[j,i]=1-r*y[i]; p[j,k]=r*y[i]
    return p


def chain(q,d,beta,a,b,r):
    rows=np.eye(q)[[a]*d]
    def ratio(t):
        trial=rows.copy(); trial[j]=(1-t)*np.eye(q)[a]+t*np.eye(q)[b]
        y=bp(trial,beta)
        return y[0]/y[1]-r
    for j in range(d):
        if ratio(0)<=2e-12 and ratio(1)>=-2e-12:
            t=0 if ratio(0)>=0 else 1 if ratio(1)<=0 else brentq(ratio,0,1,xtol=1e-15)
            rows[j]=(1-t)*np.eye(q)[a]+t*np.eye(q)[b]
            return rows
        rows[j]=np.eye(q)[b]
    raise ArithmeticError("ratio not on boundary chain")


def three_lift(x,d,beta):
    r=x[0]/x[1]
    high=chain(3,d,beta,0,1,r)
    low=chain(3,d,beta,2,1,r) if r>=1 else chain(3,d,beta,0,2,r)
    ah=1-(1-beta)*high; al=1-(1-beta)*low
    def path(s):
        # Log-interpolate the two factors. Correct their sum without changing their ratio.
        ab=np.exp((1-s)*np.log(ah[:,:2])+s*np.log(al[:,:2]))
        total=ab.sum(axis=1)
        ab*=np.maximum(1,(1+beta)/total)[:,None]
        return (1-np.column_stack([ab,2+beta-ab.sum(axis=1)]))/(1-beta)
    def err(s): return bp(path(s),beta)[2]-x[2]
    e0,e1=err(0),err(1)
    assert e0>=-2e-10 and e1<=2e-10,(x,d,beta,e0,e1)
    s=0 if e0<=0 else 1 if e1>=0 else brentq(err,0,1,xtol=1e-15)
    return path(s)


def main():
    rng=np.random.default_rng(4813)
    samples=[]
    output={"versions":[platform.python_version(),np.__version__,scipy.__version__]}
    output["exact_faces"]=[rational_face(q,d,b,samples) for q,d in [(4,2),(4,3),(4,6),(5,4),(6,3),(4,30)]
                           for b in [Q(1,100),Q(1,2),Q(99,100)]]
    # Exhaust every product support on the three active colours at small degree.
    support_count=0
    for d in (2,3,4):
        triangle={tuple((d-2 if i==0 else 0)+(i!=m) for i in range(3)) for m in range(3)}
        for masks in product(range(1,8),repeat=d):
            signatures={tuple(t.count(i) for i in range(3)) for t in product(*[[i for i in range(3) if mask&(1<<i)] for mask in masks])}
            on_face=signatures<=triangle
            assert not on_face or len(signatures)<3
            samples.append(["cartesian_support",d,masks,on_face,sorted(signatures) if on_face else None])
            support_count+=1
    output["product_supports"]=support_count
    zero_count=0
    for q,d in [(4,2),(5,2),(5,3),(6,4)]:
        for n in counts(q,d):
            z=n.count(0)
            assert z>=q-d and ((z==q-d)==(max(n)<=1))
            samples.append(["zero_signature",q,d,n,z]);zero_count+=1
        mean=[Q(1,(d+1)*(q-d))]*(d+1)+[Q(1,q-d)]*(q-d-1)
        assert sum(mean)==1 and all(v>0 for v in mean)
    output["sparse_zero_signatures"]=zero_count
    stress=np.random.default_rng(40963)
    for d in (96,384,1000):
        for beta in (Q(1,1000),Q(999,1000)):
            exps=[(d-2,1,1,0),(d-1,0,1,0),(d-1,1,0,0),(0,0,d,0)]+[tuple(map(int,stress.multinomial(d,[.25]*4))) for _ in range(12)]
            for n in exps:
                val=sum(beta**(n[i]-(d-2 if i==0 else 0)) for i in range(3))-(1+2*beta)*beta**n[3]
                assert val>=0 and ((val==0)==(n in exps[:3]))
                samples.append(["large_degree",d,str(beta),n,hex(val.numerator),hex(val.denominator)])
    output["large_degree_tests"]=96
    hullrows=[]; fit=[]
    for d in [1,2,3,7,13]:
        for beta in [.035,.5,.99]:
            ns=np.array(list(counts(3,d)))
            v=beta**ns; v/=v.sum(axis=1)[:,None]
            h=ConvexHull(v[:,:2])
            exact=exact_polygon(ns,Q(str(beta)))
            assert set(exact)=={i for i,n in enumerate(ns) if min(n)==0}
            samples.append(["polygon",d,beta,ns.tolist(),exact,h.vertices.tolist()])
            bad=0.; minp=1.
            for _ in range(24):
                weights=rng.dirichlet(np.ones(3)); ids=rng.choice(exact,3)
                x=weights@v[ids]; p=three_lift(x,d,beta)
                samples.append(["three_lift",d,beta,ids.tolist(),weights.tolist(),x.tolist(),p.tolist(),bp(p,beta).tolist()])
                bad=max(bad,np.max(abs(bp(p,beta)-x)));minp=min(minp,p.min())
                assert np.max(abs(p.sum(axis=1)-1))<2e-10
            assert bad<1e-9 and minp>=-2e-10
            hullrows.append({"d":d,"beta":beta,"exact_vertices":len(exact),"qhull_vertices":len(h.vertices),
                             "max_residual":float(bad),"smallest_input":float(minp)})
            if d in (2,3) and beta==.5:
                for _ in range(6):
                    x=rng.dirichlet(np.ones(len(v)))@v
                    def residual(u):
                        z=u.reshape(d,3);p=np.exp(z-z.max(axis=1)[:,None]);p/=p.sum(axis=1)[:,None]
                        return (bp(p,beta)-x)[:2]
                    initial=rng.normal(size=d*3)
                    opt=least_squares(residual,initial,max_nfev=500,gtol=1e-13)
                    samples.append(["three_optimization",d,beta,x.tolist(),initial.tolist(),opt.x.tolist(),opt.fun.tolist(),opt.nfev,opt.status])
                    fit.append(float(np.max(np.abs(opt.fun))))
    output["three_color_hulls_and_constructive_lifts"]=hullrows
    output["independent_least_squares_residuals"]=fit
    errs=[]
    for q in range(2,10):
        for d in [q-1,q,q+5]:
            for x in [np.eye(q)[0],np.full(q,1/q),np.arange(q,dtype=float)/sum(range(q)),rng.dirichlet(np.ones(q))]:
                p=zero_lift(x,d); err=np.max(abs(bp(p,0)-x));assert err<1e-11;errs.append(err)
                samples.append(["zero_lift",q,d,x.tolist(),p.tolist(),bp(p,0).tolist()])
    output["zero_lifts"]={"tested":len(errs),"worst_error":float(max(errs))}
    # Direct boundary checks for the elementary cases and undefined zero denominator.
    for q in range(2,8):
        p=rng.dirichlet(np.ones(q),size=2)
        assert np.allclose(bp(p,1),1/q)
        for b in (0,.4,1):
            assert np.allclose(bp(p[:1],b),(1-(1-b)*p[0])/(q-1+b))
        assert np.prod(1-np.eye(q),axis=0).sum()==0
    for d in [1,2,8,40]:
        for b in [.02,.5,.999]:
            ys=[bp(np.tile([t,1-t],(d,1)),b)[0] for t in np.linspace(0,1,31)]
            samples.append(["two_interval",d,b,ys])
            assert np.all(np.diff(ys)<=1e-14) and np.isclose(ys[-1],b**d/(1+b**d))
    output["status"]="PASS"
    path=Path(__file__).resolve().parent/"results"/"computations.json"
    with gzip.GzipFile(str(path.with_name("computational-samples.jsonl.gz")),"wb",mtime=0) as f:
        for row in samples:
            f.write((json.dumps(row,separators=(",",":"))+"\n").encode())
    with gzip.open(path.with_name("computational-samples.jsonl.gz"),"rt") as f:
        assert sum(1 for line in f if json.loads(line))==len(samples)
    output["sample_records"]=len(samples)
    path.write_text(json.dumps(output,indent=2)+"\n",encoding="utf8")
    print(f"PASS: {sum(a['tested'] for a in output['exact_faces'])} exact signatures; {len(hullrows)*24} three-colour targets; {len(errs)} zero-temperature targets.")

if __name__=="__main__":
    main()
