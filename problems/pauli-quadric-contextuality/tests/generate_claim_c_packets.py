"""Align orbit witnesses with the exact rows of the two finite census levels."""
import json,sys
from pathlib import Path
from collections import defaultdict
from zipfile import ZipFile
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_paths import table_rows
from generate_claim_c_certificates import ROOT,OUT,read,sym
from generate_claim_c_census import inst

def coord(x,free):
    return sum((x>>p&1)<<j for j,p in enumerate(free))
def chain(fn,xs):
    if len(xs)==1:return xs[0]
    return fn+' '+xs[0]+' ('+chain(fn,xs[1:])+')'
def packet(stem,ns,onH,targets,rows):
    head=['import Quadric.Five.Packets','import Quadric.Five.Resources.ProfileMasks','','namespace '+ns,
          'open Quadric.Five.Moves Quadric.Five.Moves.Data',
          'set_option Elab.async false','set_option maxRecDepth 16384','set_option maxHeartbeats 20000000']
    for start,vals in rows.items():
        parts=[]
        for j in range(0,len(vals),64):
            chunk=vals[j:j+64];n=f'part{start}_{j//64}';parts.append(n)
            ds=';'.join(','.join(map(str,[x,y,*w])) for x,y,w in chunk)
            head+=['private noncomputable def '+n+' : List Witness := witnesses% '+json.dumps(ds),
                   f'private theorem valid{n} : {n}.all (validRecord {onH} {targets})=true := by decide +kernel']
        head += [f'noncomputable def records{start} : List Witness := '+(' ++ '.join(parts) if parts else '[]'),
                 f'theorem accepted{start} : records{start}.all (validRecord {onH} {targets})=true := by']
        if not parts: head+=['  rfl']
        elif len(parts)==1: head+=['  exact valid'+parts[0]]
        else:head+=['  unfold records'+str(start)+'; simp only [List.all_append,'+','.join('valid'+p for p in parts)+',Bool.and_self]']
    head+=['end '+ns];(OUT/(stem+'.lean')).write_text('\n'.join(head)+'\n',encoding='utf8')
def bridge(stem,pkt,ns,case,starts,H,counts=None):
    C='Quadric.Five.Census.'
    space=C+('LevelOne' if H else 'Block.Case%02d'%case)
    t='hProfiles' if H else 'fullProfiles'
    head=['import Quadric.Five.Resources.'+pkt,'import Quadric.Five.Resources.'+('LevelOne' if H else 'LevelTwo%02d'%case),
          'namespace '+ns,'open Quadric.Five.Census Quadric.Five.Moves Quadric.Five.Moves.Data',
          'set_option maxRecDepth 16384','set_option maxHeartbeats 20000000','set_option Elab.async false']
    def dense(h):
        return counts is not None and sum(counts.get(h+j,0) for j in range(32))>3000
    dense_rows=[h for h in starts if dense(h)]
    heavy=[]
    if dense_rows:
        prefix=stem+'Rows'
        deps=sorted({pkt+'Part'+str((h%512)//128) for h in dense_rows})
        heavy=['import Quadric.Five.PacketSlices',*['import Quadric.Five.Resources.'+d for d in deps],
               *head[1:]]
        head.insert(0,'import Quadric.Five.Resources.'+prefix)
    for h in starts:
        if dense(h):
            rows=f'{space}.row{h}';free=f'{space}.freePoints';rep=f'{space}.restriction';offset=0
            for j in range(32):
                size=counts.get(h+j,0)
                heavy += [f"private theorem slice{h+j} : CertifiedList false fullProfiles (codeRow {free} {rep} {h+j} ({rows}[{j}]'(by decide +kernel))) :=",
                    f'  certify_slice records{h} {offset} {size} (by decide +kernel) accepted{h}']
                offset+=size
            heavy += [f'private theorem cells{h} : RowCoverage fullProfiles {free} {rep} {h} {rows} :=',
                     '  ⟨'+','.join('slice'+str(h+j) for j in range(32))+', trivial⟩',
                     f'theorem cover{h} : CertifiedList false fullProfiles (secondCodes {free} {rep} {h} {rows}) :=',
                     f'  row_coverage_sound cells{h}']
            continue
        if H: expr=f'firstCodes {space}.freePoints {h} {space}.chunk{h//32}'
        else: expr=f'secondCodes {space}.freePoints {space}.restriction {h} {space}.row{h}'
        head += [f'theorem cover{h} : CertifiedList '+('true' if H else 'false')+f' {t} ({expr}) :=',
                 f'  certify_packet records{h} (by decide +kernel) accepted{h}']
    if dense_rows:
        heavy+=['end '+ns]
        (OUT/(prefix+'.lean')).write_text('\n'.join(heavy)+'\n',encoding='utf8')
    head+=['end '+ns];(OUT/(stem+'.lean')).write_text('\n'.join(head)+'\n',encoding='utf8')
def main():
    words=table_rows();hfree=[p for p in range(1,64) if not sym(3,36,p) and p not in [1,2,8,9,16,36]]
    cp={x:(x,y,w) for x,y,w in words[1]}
    with ZipFile(ROOT/'sources/jonah-proof.zip') as z:cs=[inst(z,i) for i in range(18)]
    profiles=[c[1] for c in cs];sig=[r['sigma'] for r in read()[0]]
    (OUT/'ProfileMasks.lean').write_text('namespace Quadric.Five.Moves.Data\ndef hProfiles : List Nat := '+str(profiles)+
       '\ndef fullProfiles : List Nat := '+str(sig)+'\nend Quadric.Five.Moves.Data\n',encoding='utf8')
    order=sorted(words[0],key=lambda z:coord(z[0],hfree))
    for i in range(16):
        h=i*32;stem='HPacket%02d'%i;ns='Quadric.Five.Moves.'+stem
        vals=[v for v in order if (coord(v[0],hfree)>>16)//32==i]
        packet(stem,ns,'true','hProfiles',{h:vals});bridge('HBridge%02d'%i,stem,ns,0,[h],True)
    for ci,(_,rep,K,free,coords) in enumerate(cs):
        groups={i:[] for i in range(0,2048,32)}
        high_counts=defaultdict(int)
        for x in coords:high_counts[x>>20]+=1
        for x in sorted(coords,key=lambda t:(t>>20,t&1023,t>>10&1023)):
            v=rep|sum((x>>j&1)<<p for j,p in enumerate(free))
            groups[(x>>20)//32*32].append(cp[v])
        for g in range(4):
            stem='RPacket%02d_%d'%(ci,g);ns='Quadric.Five.Moves.'+stem
            part={h:v for h,v in groups.items() if (h//512)==g}
            if ci==15 and g<2:
                names=[]
                for lane in range(4):
                    name=stem+'Part'+str(lane)
                    selected={h:v for h,v in part.items() if (h%512)//128==lane}
                    packet(name,ns,'false','fullProfiles',selected);names.append(name)
                (OUT/(stem+'.lean')).write_text('\n'.join('import Quadric.Five.Resources.'+n for n in names)+'\n',encoding='utf8')
            else:
                packet(stem,ns,'false','fullProfiles',part)
            bridge('RBridge%02d_%d'%(ci,g),stem,ns,ci,list(part),False,high_counts)
    print('Generated aligned word packets for',len(words[0]),'hyperplane and',len(cp),'completion witnesses')
if __name__=='__main__':main()

