"""Translate 18 deposited outside-edge systems into checkable packed rows and lookup tables.

Only the declarations proved by Lean establish coverage. NumPy supplies candidates and lower
bounds. Arithmetic in the Lean verifier rechecks both and excludes every omitted assignment.
"""
from collections import defaultdict
from pathlib import Path
from zipfile import ZipFile
import argparse,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_census import ROOT,inst,syslit,bit_positions,lst,boolean
OUT=ROOT/"lean/Quadric/Five/Resources"
def tab_fields(forms):
    lo=10; N=1<<lo
    ones=((1<<(10*N))-1)//1023
    stripes=[]
    for i in range(lo):
        half=(1<<(10*(1<<i)))
        stripes.append(ones//(half+1)*half)
    tiny=[{} for _ in range(2)]
    def lowbits(m,b):
        if m not in tiny[b]:
            v=ones if b else 0
            for i in bit_positions(m):v^=stripes[i]
            tiny[b][m]=v
        return tiny[b][m]
    grouped=defaultdict(list)
    for m,s in forms:
        l=m%N; h=m//N
        assert l
        if h:
            pos=bit_positions(h);assert len(pos)==1
            ofs=(pos[0]//4)*4; width=min(4,tab_fields.hw-ofs)
        else: ofs,width=0,0
        grouped[ofs,width].append((l,h>>ofs,s))
    rows=[]
    for (ofs,width),fs in sorted(grouped.items()):
        data=[sum(lowbits(l,((g&j).bit_count()%2)^s) for l,g,s in fs) for j in range(1<<width)]
        rows.append(','.join(map(str,[ofs,width,*data])))
    return ';'.join(rows)
def rows_for(fs,K,wins):
    import numpy as np
    H=np.arange(2048,dtype=np.uint32); V=np.arange(1024,dtype=np.uint32)
    ch=np.zeros(len(H),dtype=np.int16)
    av=np.zeros((len(H),len(V)),dtype=np.uint8);bv=np.zeros_like(av)
    cv=np.zeros((len(V),len(V)),dtype=np.uint8)
    lists=[[],[],[],[]]
    for mask,s in fs:
        a=mask%1024;b=(mask>>10)%1024; h=mask>>20
        f=(np.bitwise_count(H&h)&1)^s;u=np.bitwise_count(V&a)&1;v=np.bitwise_count(V&b)&1
        if not a and not b: ch+=f;lists[3].append((h,s))
        elif not b: av+=f[:,None]^u;lists[0].append((h<<10|a,s))
        elif not a: bv+=f[:,None]^v;lists[1].append((h<<10|b,s))
        else:
            assert not h
            cv+=(u[:,None]^v)^s; lists[2].append((a<<10|b,s))
    low=cv.min(axis=1);minb=bv.min(axis=1)
    eligible=ch[:,None]+av+minb[:,None]+low<=K
    w=defaultdict(list)
    for x in wins:
        h=x>>20;b=x>>10&1023;a=x&1023
        assert eligible[h,a] and ch[h]+int(av[h,a])+int(bv[h,b])+int(cv[a,b])<=K
        w[h,a].append(b)
    rows=[]
    for h in range(2048):
        slices=[','.join(map(str,[a,*sorted(w[h,int(a)])])) for a in np.flatnonzero(eligible[h])]
        rows.append('|'.join([str(minb[h]),*slices]))
    return lists,low,rows

def create(i,start,n,pilot):
    with ZipFile(ROOT/'sources/jonah-proof.zip') as z: fs,rep,K,free,surv=inst(z,i)
    ls,low,rows=rows_for(fs,K,surv)
    nm=f'{i:02d}';ns='Quadric.Five.Census.Block.Case'+nm
    opts=['set_option maxRecDepth 16384','set_option maxHeartbeats 24000000','set_option Elab.async false']
    src=['import Quadric.Five.BlockLiterals','','namespace '+ns,*opts]
    sysfields=[syslit(v,10,h) for v,h in zip(ls[:3],(11,11,10))]
    hi=lst(['('+lst(bit_positions(h))+','+boolean(s)+')' for h,s in ls[3]])
    src+=['noncomputable def system : Split := ⟨'+',\n'.join(sysfields+[hi,str(K),lst(low),'[]'])+'⟩',
          f'def restriction : ℕ := {rep}', 'def freePoints : List ℕ := '+str(free)]
    packed_min=sum(int(v)<<(10*j) for j,v in enumerate(low))
    for j,(v,k,key) in enumerate(zip(ls[:3],(11,11,10),('first','second','crossBlock'))):
        tab_fields.hw=k
        src+=['noncomputable def t'+str(j)+' : Tables := tables% '+json.dumps(tab_fields(v)),
              f'theorem table{j} : buildT system.{key}=t{j} := by decide +kernel']
    src+=['end '+ns]
    (OUT/('System'+nm+'.lean')).write_text('\n'.join(src)+'\n',encoding='utf8')
    prep=['import Quadric.Five.Intervals','import Quadric.Five.Resources.System'+nm,'','namespace '+ns,*opts]
    pc=32
    for start_at in range(0,1024,pc):
        prep+=[f'private theorem cross{start_at} : Interval (crossCheck system t2) {start_at} {pc} :=',
               '  interval_checked (by decide +kernel)']
    pr='cross'+str(1024-pc)
    for pos in reversed(range(0,1024-pc,pc)): pr=f'Interval.join cross{pos} ({pr})'
    prep+=['theorem prep : prepared system (buildT system.crossBlock)=true := by',
           '  rw [table2]; apply prepare_parts system t2 (by decide +kernel)',
           '  exact '+pr,'end '+ns]
    (OUT/('Prepare'+nm+'.lean')).write_text('\n'.join(prep)+'\n',encoding='utf8')
    numeric=['import Quadric.Five.Intervals','import Quadric.Five.Resources.System'+nm,'','namespace '+ns,*opts,
        f'private theorem cachedMinimum : packList system.lowFirst={packed_min} := by decide +kernel']
    leaves=[]
    for h in range(start,start+n,32):
        part=rows[h:min(start+n,h+32)]; c='row'+str(h); m=len(part); seg='leaf'+str(h)
        numeric+=['noncomputable def '+c+' : List Row := blockRows% '+json.dumps('/'.join(part)),
                  f'theorem {seg} : Segment system t0 t1 t2 {h} {m} {c} := by',
                  f'  refine ⟨by decide +kernel,?_⟩; rw [cache_run,cachedMinimum]; decide +kernel']
        leaves.append((c,seg,h,m))
    numeric+=['end '+ns]
    if pilot:
        out=numeric[:-1]
    else:
        (OUT/('RChecked'+nm+'.lean')).write_text('\n'.join(numeric)+'\n',encoding='utf8')
        out=['import Quadric.Five.Resources.RChecked'+nm,'import Quadric.Five.Resources.Prepare'+nm,'','namespace '+ns,*opts]
    if pilot: out[0]='import Quadric.Five.Resources.Prepare'+nm
    while len(leaves)>1:
        new=[]
        for j in range(0,len(leaves),2):
            if j+1==len(leaves): new.append(leaves[j]);continue
            l,pl,h,u=leaves[j];r,pr,_,v=leaves[j+1];name=f'group{h}_{u+v}';proof='checked'+name
            out += [f'noncomputable def {name} := {l} ++ {r}',
                    f'private theorem {proof} : Segment system t0 t1 t2 {h} {u+v} {name} :=',
                    f'  @Segment.join system t0 t1 t2 {h} {u} {v} {l} {r} {pl} {pr}']
            new.append((name,proof,h,u+v))
        leaves=new
    rootname,proof,_,_=leaves[0]
    out += [f'noncomputable def rows := {rootname}',
            f'theorem accepted : run system t0 t1 t2 {start} rows=true := {proof}.2',
            f'theorem rows_length : rows.length={n} := {proof}.1',
            f'theorem coverage (h a b : ℕ) (hh : h<{n}) (ha : a<1024) (hb : b<1024) :',
            f"    fullCost system ({start}+h) a b ≤ system.cutoff ↔ member (rows[h]'(rows_length.symm ▸ hh)) a b := by",
            f'  have ok : run system (buildT system.first) (buildT system.second) (buildT system.crossBlock) {start} rows=true := by rw [table0,table1,table2]; exact accepted',
            f'  exact run_sound system prep {start} rows ok h a b (rows_length.symm ▸ hh) ha hb','end '+ns]
    fn=(ROOT/'.work'/f'BlockPilot{nm}.lean') if pilot else (OUT/('LevelTwo'+nm+'.lean'))
    fn.parent.mkdir(parents=True,exist_ok=True)
    fn.write_text('\n'.join(out)+'\n',encoding='utf8')
    print(i,'rows',n,'claimed hits in whole case',len(surv),'system bytes',sum(map(len,src)),'rows bytes',sum(map(len,out)),flush=True)
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--case',type=int,action='append');ap.add_argument('--start',type=int,default=0)
    ap.add_argument('--pilot',type=int);args=ap.parse_args()
    assert args.start>=0 and (args.pilot or 2048)+args.start<=2048
    for c in args.case or range(18): create(c,args.start,args.pilot or 2048,args.pilot is not None)
