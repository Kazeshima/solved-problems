"""Serialize signed Pauli triples and proposed intermediate duplicate-check states for Lean."""
from pathlib import Path
import json, itertools, sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import ROOT, OUT, phase, sym, ys

def make():
    inner=[(a,b,a^b,phase(3,a,b)//2) for a in range(1,64) for b in range(1,64)
           if a<b<a^b and sym(3,a,b)==0]
    outside=[p for p in range(1,256) if (ys(4,p)%2)==sym(4,17,p) and sym(4,1,p)]
    def drop(p): return (p%16)//2+8*((p//16)//2)
    outer=[(drop(u^v),64+i,64+j,phase(4,u,v)//2) for i,u in enumerate(outside)
           for j,v in enumerate(outside) if i<j and not sym(4,u,v)]
    assert len(inner)==315 and len(outer)==756
    def label(i): return (ys(3,i)%2+2*(i%8)+32*(i//8)) if i<64 else outside[i-64]
    h=['import Quadric.Five.Catalogue','import Quadric.Five.Reduction','',
       'namespace Quadric.Five.Tagged.Data','open Small','set_option Elab.async false',
       'set_option maxRecDepth 16384','set_option maxHeartbeats 16000000']
    src=h[:]; seg=[[],[]]; proofs=[[],[]]; traces=[[],[]]; seen=0; k=0
    src+=['private def seen0 : ℕ := 0']
    for b,ls in enumerate([inner,outer]):
        for start in range(0,len(ls),16):
            chunk=ls[start:start+16]
            nm=f'triples{k}'; seg[b].append(nm)
            src.append('private noncomputable def '+nm+' : List Line := signedLines% '+json.dumps(';'.join(','.join(map(str,l)) for l in chunk)))
            for a,q,t,n in chunk:
                for v,w,_ in itertools.permutations((a,q,t)):
                    key=label(v)+256*label(w); assert not (seen>>key&1); seen|=1<<key
            src+=['private def seen'+str(k+1)+' : ℕ := '+hex(seen),
                  f'private theorem valid{k} : Valid '+('false' if b else 'true')+f' {nm} := by unfold Valid; decide +kernel',
                  f'private theorem distinct{k} : Trace {nm} seen{k} seen{k+1} := by unfold Trace; decide +kernel']
            proofs[b].append(f'valid{k}');traces[b].append(f'distinct{k}');k+=1
    def chain(fn,ps):
        if len(ps)==1:return ps[0]
        mid=len(ps)//2;left=chain(fn,ps[:mid]);right=chain(fn,ps[mid:])
        return f'({left} ++ {right})' if fn=='append' else f'({fn} {left} {right})'
    for b,name in enumerate(['inside','outside']):
        orig=['full3','outsideLines'][b]; cat=chain('append',seg[b]); value=['true','false'][b]
        src+=[f'private noncomputable def {name} := '+cat,
              f'private theorem {name}Eq : {orig}={name} := by']
        if b: src+=['  unfold outsideLines outsideLine isEdge','  rw [←outside_coordinates]']
        src+=['  decide +kernel',f'private theorem {name}VR : Valid {value} {name} := '+chain('Valid.append',proofs[b])]
        p=0 if not b else len(seg[0]); q=p+len(seg[b])
        src+=[f'private theorem {name}TR : Trace {name} seen{p} seen{q} := '+chain('Trace.append',traces[b])]
    src+=['theorem valid_inner : Valid true full3 := insideEq.symm ▸ insideVR',
          'theorem distinct_inner : fresh 0 ((full3.flatMap six).map key)=true := by rw [insideEq]; exact insideTR.unique',
          'theorem valid_all : Valid false ellipticLines := by rw [ellipticLines,insideEq,outsideEq]; exact insideVR.weaken.append outsideVR',
          'theorem distinct_all : fresh 0 ((ellipticLines.flatMap six).map key)=true := by',
          '  rw [ellipticLines,insideEq,outsideEq]; exact (insideTR.append outsideTR).unique',
          'theorem exact_if_complete (h : EllipticCompletions) : degree 5=6975 :=',
          '  exact_of_catalogues valid_inner distinct_inner valid_all distinct_all h','end Quadric.Five.Tagged.Data']
    geom=['import Quadric.Five.Hyperplanes','import Quadric.Five.Catalogue',
          'namespace Quadric.Five.Small.HyperplaneData','set_option maxRecDepth 8192',
          'set_option maxHeartbeats 4000000','set_option Elab.async false']
    geom += [l for l in src if any(l.startswith('private noncomputable def '+n+' ') for n in seg[0])]
    for j,n in enumerate(seg[0]):
        geom += [f'private theorem fifteen{j} : {n}.all (fun l=>multiplicity l==15)=true := by decide +kernel']
    geom+=['private theorem splitLines : full3='+' ++ '.join(seg[0])+' := by decide +kernel',
        'theorem fifteen_per_line : ∀l∈full3,multiplicity l=15 := by',
        '  have h : full3.all (fun l=>multiplicity l==15)=true := by',
        '    rw [splitLines]; simp only [List.all_append,'+','.join(f'fifteen{j}' for j in range(len(seg[0])))+',Bool.and_self]',
        '  exact fun l hl=>eq_of_beq (List.all_eq_true.mp h l hl)',
        'theorem low_section {s : ℕ→Bool} (low : errors full3 s≤92) :',
        '    ∃u∈hyperplanes,hyperErrors s u≤21 := cheap_hyperplane s low fifteen_per_line',
        'end Quadric.Five.Small.HyperplaneData']
    (OUT/'HyperplaneData.lean').write_text('\n'.join(geom)+'\n',encoding='utf8')
    masks=h[:]
    masks += [l.removeprefix('private ') for l in src if l.startswith('private def seen')]
    masks += ['end Quadric.Five.Tagged.Data']
    (OUT/'TagMasks.lean').write_text('\n'.join(masks)+'\n',encoding='utf8')
    stop=src.index(next(l for l in src if l.startswith('private noncomputable def inside :=')))
    imports=[]
    for i in range(0,k,4):
        module=f'TagBlock{i//4:02d}'; imports.append('import Quadric.Five.Resources.'+module)
        dest=['import Quadric.Five.Resources.TagMasks',*h[2:]]
        for j in range(i,min(i+4,k)):
            for prefix in (f'private noncomputable def triples{j} ',f'private theorem valid{j} ',f'private theorem distinct{j} '):
                dest.append(next(l for l in src[:stop] if l.startswith(prefix)).removeprefix('private '))
        dest+=['end Quadric.Five.Tagged.Data']
        (OUT/(module+'.lean')).write_text('\n'.join(dest)+'\n',encoding='utf8')
    return '\n'.join(imports+h+src[stop:])+'\n'
if __name__=='__main__':
    (OUT/'TaggedLines.lean').write_text(make(),encoding='utf8')
