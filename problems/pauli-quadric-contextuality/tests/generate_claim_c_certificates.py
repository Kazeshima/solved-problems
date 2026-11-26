"""Translate the public 42 integer certificates into Lean data. Lean checks matrix reconstruction,
positive pivots and the bound separately. The generator is outside the trusted proof."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
import argparse

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/"lean/Quadric/Five/Resources"
def read():
    zfile=ROOT/"sources/jonah-evidence.zip"
    with ZipFile(zfile) as z:
        name=next(n for n in z.namelist() if n.endswith("/cert/L7R_CERTS_42.txt"))
        data=z.read(name)
    blocks=[]; t=None
    for line in data.decode("ascii").splitlines():
        fields=line.split()
        if not fields:continue
        k=fields[0]
        if k=="ORBIT": t={"id":int(fields[1]),"tri":[]}
        elif k=="SIGMA": t["sigma"]=int(fields[1],16)
        elif k=="N": t["count"]=int(fields[1])
        elif k=="DEN": t["den"]=int(fields[1])
        elif k=="Y": t["y"]=list(map(int,fields[1:]))
        elif k=="TRI": t["nt"]=int(fields[1])
        elif k=="B": t["B"]=Fraction(fields[1])
        elif k=="FCERT": t["floor"]=int(fields[1])
        elif k=="METHOD": t["method"]=fields[1]
        elif k=="END":
            assert len(t["y"])==56 and t["nt"]==len(t["tri"]) and t["id"]==len(blocks)
            blocks.append(t)
        else: t["tri"].append(tuple(map(int,fields)))
    assert len(blocks)==42
    return blocks,sha256(data).hexdigest()
def parts(n,v):return v%(1<<n),v>>n
def ys(n,v):
    a,b=parts(n,v); return (a&b).bit_count()
def phase(n,p,r):
    a,b=parts(n,p);c,h=parts(n,r)
    return (ys(n,p)+ys(n,r)-ys(n,p^r)+2*(b&c).bit_count())%4
def sym(n,p,r):
    a,b=parts(n,p);c,h=parts(n,r)
    return ((a&h).bit_count()+(b&c).bit_count())%2
def matrix(rec):
    sig=rec["sigma"];d=rec["den"]
    O=[i for i in range(1,256) if (ys(4,i)%2)==sym(4,17,i) and sym(4,1,i)]
    assert len(O)==56
    def G(p,q):
        if p==q or sym(4,p,q):return 0
        x,z=parts(4,p^q);w=(x>>1)+8*(z>>1)
        return (-1)**((phase(4,p,q)//2)^(sig>>w&1))
    g=[[G(p,q) for q in O] for p in O]
    m=[[2*rec["y"][i] if i==j else -2*d*g[i][j] for j in range(i,56)] for i in range(56)]
    for a,b,c,u in rec["tri"]:
        assert a<b<c and u>=0 and g[a][b]*g[b][c]*g[a][c]==-1
        for i,j in ((a,b),(a,c),(b,c)):m[i][j-i]+=u*g[i][j]
    return m
def lvec(v):return "["+",".join(map(str,v))+"]"
def lmat(m):return "[\n"+",\n".join("  "+lvec(v) for v in m)+"]"
def pivot(d,a):
    p=a[0][0];v=a[0][1:]
    assert p>0
    new=[]
    for i,row in enumerate(a[1:]):
        out=[]
        for j,entry in enumerate(row,i):
            q,r=divmod(p*entry-v[i]*v[j],d)
            assert not r
            out.append(q)
        new.append(out)
    return p,new
def write_record(rec):
    i=rec["id"]; tname=f"cert{i:02d}"
    fl="["+",\n".join("⟨"+",".join(map(str,t))+"⟩" for t in rec["tri"])+"]"
    b=rec["B"]
    return (f"def {tname} : Cert :=\n  ⟨{rec['sigma']},{rec['count']},{rec['den']},"
            f"{lvec(rec['y'])},\n    {fl},{b.numerator},{b.denominator},{rec['floor']}⟩\n")
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--pilot",type=int)
    args=ap.parse_args()
    recs,h=read()
    if args.pilot is not None:
        (ROOT/'.work').mkdir(exist_ok=True)
        t=recs[args.pilot];m=matrix(t);n="PdPilot"+str(args.pilot)
        text=("import Quadric.Five.Elimination\nnamespace "+n+"\nset_option maxRecDepth 16384\n"
          +"set_option maxHeartbeats 12000000\ndef m : List (List ℤ) := "+lmat(m)+"\n"
          +"theorem checked : Quadric.Five.Schur.check 56 1 m = true := by decide +kernel\nend "+n+"\n")
        (ROOT/".work"/(n+".lean")).write_text(text,encoding="utf8")
        return
    print("42 records; original certificate text SHA256",h)
if __name__=="__main__":main()
