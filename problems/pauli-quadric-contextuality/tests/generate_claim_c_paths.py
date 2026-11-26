"""Extend each deposited orbit word by explicit physical gauges and verify the representative it reaches."""
from pathlib import Path
from zipfile import ZipFile
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import ROOT,sym,read
from generate_claim_c_moves import move

def step(data,x):
    src,twist,active,stages=data
    q=x
    for d,mask in reversed(stages): q=((q>>d)&mask)|((q&mask)<<d)
    return (((q^x)&active)^x^twist) & ((1<<64)-1)
def setup():
    moves=[move(k) for k in range(72)]
    hm=sum(1<<p for p in range(1,64) if sym(3,36,p)==0)
    gauges={}
    for k in range(128):
        w=[64+t for t in range(7) if k>>t&1]
        q=0
        for t in w:q=step(moves[t],q)
        gauges[q]=w
    assert len(gauges)==128
    return moves,hm,gauges
def table_rows():
    mv,hm,g=setup(); canon=[r['sigma'] for r in read()[0]]
    hg={x&hm:w for x,w in g.items()}
    out=[[],[]]
    with ZipFile(ROOT/'sources/jonah-proof.zip') as z:
        for t,f in enumerate(['level1_words.tsv','closure_words.tsv']):
            for line in z.read('CPL/data/'+f).decode().splitlines():
                x,y,w=line.split('\t'); q=x=int(x,16); gen=[int(c) for c in w.split(',') if c]
                y=int(y,16) if t==0 else canon[int(y)]
                for c in gen:
                    assert t or (sym(3,c,36)==0)
                    q=step(mv[c],q)
                extra=g[q^y] if t else hg[(q^y)&hm]
                gen=gen+extra
                for c in extra:q=step(mv[c],q)
                assert (q if t else q&hm)==y
                out[t].append((x,y,gen))
    return out
def main():
    for label,records in zip(('normalized hyperplane assignments','normalized completions'),table_rows()):
        print(label,len(records),'verified generator applications',sum(len(w) for _,_,w in records))
    return 0

if __name__=='__main__':raise SystemExit(main())
