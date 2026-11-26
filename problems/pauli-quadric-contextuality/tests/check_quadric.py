"""Independent exact checks. Python 3.10+ standard library."""
from itertools import combinations, product
from collections import Counter
from random import Random
from pathlib import Path
import gzip
import json

LOG = Path(__file__).resolve().parents[1] / 'logs'

def dot(x, y):
    return (x & y).bit_count() % 2

def geometry(n):
    d = 1 << n
    points = [(a,b) for a,b in product(range(d),repeat=2) if (a or b) and not dot(a,b)]
    rows = []
    for p,r in combinations(points,2):
        a,b=p; c,e=r
        z=(a^c,b^e)
        if r < z and dot(a,e)==dot(b,c):
            rows.append((p,r,z,dot(b,c)))
    assert 2*len(points)==(d-1)*(d+2)
    assert 48*len(rows)==(d-1)*(d-2)*(d+2)*(d+4)
    return points,rows

def matrix(n, points, signs):
    d=1<<n
    a=[[0]*d for _ in range(d)]
    for u,b in points:
        for x in range(d):
            a[x^u][x] += (-1)**(signs[u,b]^dot(b,x))
    assert all(a[i][j]==a[j][i] for i,j in product(range(d),repeat=2))
    return a

def moments(n, pts, lines, s):
    d=1<<n
    a=matrix(n,pts,s)
    a2=[[sum(x*y for x,y in zip(row,col)) for col in a] for row in a]
    t1=sum(a[x][x] for x in range(d))
    t2=sum(a2[x][x] for x in range(d))
    t3=sum(a2[x][y]*a[y][x] for x,y in product(range(d),repeat=2))
    bad=sum(s[p]^s[r]^s[z]^c for p,r,z,c in lines)
    assert (t1,t2,t3)==(0,d*len(pts),6*d*(len(lines)-2*bad))
    g=len(lines)-2*bad
    assert (d+4)**2*g*g <= 8*(d+2)*len(lines)**2
    return bad

def tensor_phases(n, lines):
    # Standard Hermitian matrices, with each local label encoded as x + 2*z.
    paulis = [
        ((1,0),(0,1)), ((0,1),(1,0)), ((1,0),(0,-1)), ((0,-1j),(1j,0))
    ]
    def multiply(a,b):
        return tuple(tuple(sum(a[i][k]*b[k][j] for k in (0,1))
                           for j in (0,1)) for i in (0,1))
    local = {}
    for u,v in product(range(4),repeat=2):
        mat = multiply(multiply(paulis[u],paulis[v]),paulis[u^v])
        phase=mat[0][0]
        assert mat==((phase,0),(0,phase)) and phase in (1,-1,1j,-1j)
        local[u,v]=phase
    for p,r,z,c in lines:
        phase=1
        for k in range(n):
            u=(((a>>k)&1)+2*((b>>k)&1) for a,b in (p,r))
            phase*=local[tuple(u)]
        switches=sum((a&b).bit_count()//2 for a,b in (p,r,z))
        assert phase==(-1)**(c+switches)
    print("Hermitian tensor products agree on all",len(lines),"contexts")

def chart_geometry(pts, lines):
    def sym(u,v):
        return dot(u&7,v>>3)^dot(v&7,u>>3)
    def det3(a,b,c):
        return sum(((a>>i)&(b>>j)&(c>>k)&1) for i,j,k in
                   ((0,1,2),(1,2,0),(2,0,1),(2,1,0),(1,0,2),(0,2,1)))%2
    spaces={}
    for u,v,w in combinations(range(1,64),3):
        if u^v==w or sym(u,v) or sym(v,w) or sym(w,u):
            continue
        S=frozenset((u,v,w,u^v,v^w,w^u,u^v^w))
        if S in spaces:
            continue
        columns=[sum(((x>>i)&1)<<j for j,x in enumerate((u,v,w))) for i in range(6)]
        minors=[det3(*(columns[i+3*((mask>>i)&1)] for i in range(3))) for mask in range(8)]
        pack=lambda indices: sum(minors[i]<<j for j,i in enumerate(indices))
        spaces[S]=(pack((0,6,5,3)),pack((7,1,2,4)))
    assert set(spaces.values())==set(pts) and len(spaces)==135
    pencils={}
    for S,p in spaces.items():
        for u,v in combinations(sorted(S),2):
            if v<u^v:
                pencils.setdefault(frozenset((u,v,u^v)),[]).append(p)
    assert all(len(p)==3 for p in pencils.values())
    bad={frozenset((p,r,z)) for p,r,z,c in lines if
         sum(bool(a and b) for a,b in (p,r,z))%2 ^ c}
    assert set(map(frozenset,pencils.values()))==bad and len(bad)==315
    print("DW incidence: 135 Lagrangian spaces, 315 distinct pencils, equal line sets")

def orbit_check():
    # Each projective vector is an integer tuple times a common positive scale.
    # H and S use scale 1; M uses sqrt(2), in units of 1/sqrt(24).
    def orient(v):
        return tuple(v) if next(x for x in v if x)>0 else tuple(-x for x in v)
    dirs=[]
    for a in range(1,16):
        pivot=a & -a
        dirs.append([(x,x^a) for x in range(16) if not x & pivot])
    def mix(v,d,divide):
        w=[0]*16
        for i,j in d:
            w[i]=(v[i]+v[j])//divide
            w[j]=(v[i]-v[j])//divide
        return orient(w)
    masks=[(1<<i) for i in range(4)]
    masks += [a|b for a,b in combinations(masks,2)]
    patterns=[sum(1<<i for i,m in enumerate(masks) if x&m==m) for x in range(16)]
    H=set()
    for f in range(1024):
        v=[3]+[1 if dot(f,patterns[x]) else -1 for x in range(1,16)]
        for t in range(16): H.add(orient([v[x^t] for x in range(16)]))
    M={mix(v,d,2) for v in H for d in dirs}
    S=set()
    for v in M:
        heavy=next(i for i,x in enumerate(v) if abs(x)==2)
        for a,d in enumerate(dirs,1):
            if v[heavy^a]==0: S.add(mix(v,d,1))
    assert (len(H),len(M),len(S))==(16384,30720,14336)
    assert all(sum(x*x for x in v)==24 for v in H|S)
    assert all(sum(x*x for x in v)==12 for v in M)
    print("Projective integer orbits: H = 16384, M = 30720, S = 14336, total = 61440")
    remaining=H|M|S
    pts,lines=geometry(4)
    configurations=set()
    state_rows=['orbit\tcoordinates x=0..15, normalize to unit length']
    records=[]
    while remaining:
        w=min(remaining)
        translations={orient([(-1 if dot(b,x) else 1)*w[x^a] for x in range(16)])
                      for a,b in product(range(16),repeat=2)}
        assert len(translations)==256 and translations <= remaining
        remaining.difference_update(translations)
        norm=sum(x*x for x in w)
        expectations={(a,b):sum(w[x^a]*w[x]*(-1 if dot(b,x) else 1) for x in range(16))
                      for a,b in pts}
        assert all(3*abs(e)==norm for e in expectations.values())
        violated=frozenset(i for i,(p,r,z,c) in enumerate(lines) if
            (expectations[p]<0)^(expectations[r]<0)^(expectations[z]<0)^bool(c))
        assert len(violated)==315 and violated not in configurations
        configurations.add(violated)
        orbit=len(records)
        records.append({'orbit':orbit, 'representative':w, 'violated_line_indices':sorted(violated)})
        state_rows.extend(str(orbit)+'\t'+'\t'.join(map(str,state)) for state in sorted(translations))
    assert len(configurations)==240
    table=('\n'.join(state_rows)+'\n').encode('ascii')
    packed=gzip.compress(table,mtime=0)
    assert gzip.decompress(packed)==table and len(state_rows)==61441
    (LOG/'four-states.tsv.gz').write_bytes(packed)
    raw=json.dumps({'lines':lines,'orbits':records},separators=(',',':')).encode('ascii')
    packed=gzip.compress(raw,mtime=0)
    assert gzip.decompress(packed)==raw
    (LOG/'four-configurations.json.gz').write_bytes(packed)
    print("All 61440 states partition into 240 Pauli orbits of 256; 240 distinct 315-line sets")

if __name__=="__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=LOG,
                        help="directory for the two reconstructed tables")
    LOG = parser.parse_args().output_dir
    LOG.mkdir(parents=True, exist_ok=True)
    rng=Random(20261125)
    for n in range(2,6):
        pts,rows=geometry(n)
        tensor_phases(n,rows)
        canonical={p:int(all(p)) for p in pts}
        v=moments(n,pts,rows,canonical)
        assert v=={2:3,3:21,4:315,5:6975}[n]
        samples=[]
        for k in range(4):
            sample={p:rng.randrange(2) for p in pts}
            count=moments(n,pts,rows,sample)
            samples.append(count)
            mask=sum(value<<i for i,value in enumerate(sample.values()))
            print(f'sample n={n} index={k} sign_mask={mask:x} violations={count}')
        assert moments(n,pts,rows,{p:1-k for p,k in canonical.items()})==len(rows)-v
        print(f"n={n}: {len(pts)} points, {len(rows)} lines, mixed-sign violations={v}, random={samples}")
        if n==2:
            vals=[sum(((m>>pts.index(p))^(m>>pts.index(r))^(m>>pts.index(z))^c)&1
                      for p,r,z,c in rows) for m in range(1<<len(pts))]
            assert min(vals)==1 and max(vals)==5
            print("All 512 two-qubit assignments: degree=1; distribution", sorted(Counter(vals).items()))
        if n==4: chart_geometry(pts,rows)
    orbit_check()
