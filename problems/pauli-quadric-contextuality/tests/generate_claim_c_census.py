"""Prepare finite census blocks from the deposited instances and completion lists.

The input lists are candidate answers. The Lean screening checks exclude missing answers.
"""
from pathlib import Path
from zipfile import ZipFile
from collections import defaultdict
import argparse, sys

ROOT=Path(__file__).resolve().parents[1]
BASE="CPL/data/"
def bit_positions(x):
    return [i for i in range(x.bit_length()) if x>>i&1]
def lst(a):
    return "["+",".join(map(str,a))+"]"
def boolean(s):
    return "true" if s else "false"
def syslit(forms,low,high,K=0):
    pure=[]; groups=defaultdict(list)
    for m,s in forms:
        lo=m%2**low; hi=m>>low
        if not lo:
            pure.append("("+lst(bit_positions(hi))+","+boolean(s)+")")
            continue
        v=bit_positions(hi)
        if not v: o,w=0,0
        elif v[0]//4==v[-1]//4: o=4*(v[0]//4);w=min(4, high-o)
        else: o=v[0];w=v[-1]-o+1
        groups[o,w].append("⟨"+str(lo)+","+lst([j-o for j in v])+","+boolean(s)+"⟩")
    values=["⟨"+str(o)+","+str(w)+","+lst(fs)+"⟩" for (o,w),fs in sorted(groups.items())]
    return "⟨"+str(low)+","+str(high)+","+str(K)+","+lst(pure)+",\n"+lst(values)+"⟩"
def inst(z,i):
    data=z.read(BASE+"level2_inst_%02d.txt"%i).decode().splitlines()
    _,r0,rep,K=data[0].split();r0=int(r0);rep=int(rep,16);K=int(K)
    vs=list(map(int,data[1].split()))
    assert len(set(vs))==31 and r0 not in vs
    def bit(p):return 0 if p==r0 else 1<<vs.index(p)
    forms=[]
    for l in data[2:]:
        h,p,q,s=map(int,l.split());forms.append((bit(p)^bit(q),s^(rep>>h&1)))
    full=[int(l,16) for l in z.read(BASE+"level2_comp_%02d.txt"%i).decode().splitlines()]
    ans=[sum((s>>p&1)<<j for j,p in enumerate(vs)) for s in full]
    return forms,rep,K,vs,ans
def screen(forms,K,ans):
    import numpy as np
    hv=np.arange(32768,dtype=np.uint32);av=np.arange(256,dtype=np.uint32)
    hc=np.zeros(32768,dtype=np.int16)
    ma=np.zeros((32768,256),dtype=np.uint8);mb=np.zeros_like(ma);mc=np.zeros((256,256),dtype=np.uint8)
    A=[];B=[];C=[];H=[]
    for m,s in forms:
        h=m>>16;a=m&255;b=(m>>8)&255
        vh=(np.bitwise_count(hv&h)&1)^s; va=np.bitwise_count(av&a)&1;vb=np.bitwise_count(av&b)&1
        if not a and not b:hc+=vh;H.append((h,s))
        elif not b:ma+=vh[:,None]^va[None,:];A.append((h<<8|a,s))
        elif not a:mb+=vh[:,None]^vb[None,:];B.append((h<<8|b,s))
        else:
            assert h==0
            mc+=(va[:,None]^vb[None,:])^s;C.append((a<<8|b,s))
    aMin=ma.min(axis=1);bMin=mb.min(axis=1)
    caMin=mc.min(axis=1);cbMin=mc.min(axis=0)
    ca=(hc[:,None]+ma+bMin[:,None]+caMin[None,:])<=K
    cb=(hc[:,None]+mb+aMin[:,None]+cbMin[None,:])<=K
    source="⟨"+syslit(A,8,15)+",\n"+syslit(B,8,15)+",\n"+syslit(C,8,8)+",\n"+lst(
       ["("+lst(bit_positions(h))+","+boolean(s)+")" for h,s in H])+","+str(K)+",\n"+lst(caMin)+","+lst(cbMin)+"⟩"
    wins=defaultdict(list)
    for x in ans:wins[x>>16].append(x&65535)
    rows=[]
    for h in range(32768):
        aa=np.flatnonzero(ca[h]);bb=np.flatnonzero(cb[h])
        assert all((w&255) in aa and (w>>8) in bb for w in wins[h])
        rows.append(f"⟨{aMin[h]},{bMin[h]},{lst(aa)},{lst(bb)},{lst(sorted(wins[h]))}⟩")
    return source,rows
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--case",type=int,default=0);ap.add_argument("--start",type=int,default=0)
    ap.add_argument("--pilot",type=int,required=True)
    args=ap.parse_args()
    with ZipFile(ROOT/"sources/jonah-proof.zip") as z: fs,rep,K,vs,ans=inst(z,args.case)
    s,rows=screen(fs,K,ans)
    name=f"ScreenPilot{args.case}_{args.start}_{args.pilot}"
    code=("import Quadric.Five.Screen\nopen Quadric.Five.Census\nnamespace "+name+"\n"+
        "set_option maxRecDepth 16384\nset_option maxHeartbeats 30000000\nset_option Elab.async false\n"+
        "def inst : Split := "+s+"\n"+"def rows : List Row := "+lst(rows[args.start:args.start+args.pilot])+"\n"+
        "theorem verified : rowChecks inst "+str(args.start)+" rows=true := by decide +kernel\nend "+name+"\n")
    (ROOT/".work").mkdir(exist_ok=True)
    (ROOT/".work"/(name+".lean")).write_text(code,encoding="utf8")
    print(name,"source bytes",len(code.encode("utf8")))
if __name__=="__main__":main()
