"""Generate signed moves on the 119 elliptic points, with their 64-bit section actions."""
from pathlib import Path
from itertools import combinations
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import ROOT,OUT,phase,sym,ys

def lift(w):return ys(3,w)%2+2*(w%8)+32*(w//8)
def physical():
    O=[p for p in range(1,256) if ys(4,p)%2==sym(4,17,p) and sym(4,p,1)]
    return [lift(w) for w in range(64)]+O
def lines():
    ps=physical(); ind={p:i for i,p in enumerate(ps)}
    inside={(a,b,a^b,phase(3,a,b)//2) for a,b in combinations(range(1,64),2) if b<a^b and not sym(3,a,b)}
    outside={(ind[ps[a]^ps[b]],a,b,phase(4,ps[a],ps[b])//2)
             for a,b in combinations(range(64,120),2) if not sym(4,ps[a],ps[b])}
    assert len(inside)==315 and len(outside)==756
    return inside,outside
def move(k):
    ps=physical(); ind={p:i for i,p in enumerate(ps)}
    src=[];ph=[]
    for i,p in enumerate(ps):
        if 0<k<64:
            t=lift(k)^1
            j=ind[p^t] if sym(4,t,p) else i
            flip= ((1+phase(4,t,ps[j]))%4)//2 if j!=i else 0
        else:
            j=i
            flip=(p>>(1,2,3,5,6,7,0)[k-64])&1 if 64<=k<71 else int(k==71 and i==0)
        src.append(j);ph.append(flip)
    active=sum((i!=src[i])<<i for i in range(64))
    stages=[]
    if 0<k<64:
        for bit in range(6):
            d=1<<bit
            if k&d:
                mask=sum(1<<i for i in range(64) if not i&d);stages.append((d,mask))
    image=sum(j<<(7*i) for i,j in enumerate(src));twist=sum(v<<i for i,v in enumerate(ph))
    assert sorted(src)==list(range(120))
    for i,j in enumerate(src[:64]):
        assert j==(i^k if active>>i&1 else i)
        if 0<k<64 and j!=i: assert ph[i]==((1+phase(3,k,j))%4)//2
    for catalogue in lines():
        mapped={(*sorted([src[a],src[b],src[c]]),f^ph[a]^ph[b]^ph[c]) for a,b,c,f in catalogue}
        assert mapped==catalogue,(k,next(iter(mapped-catalogue)))
    return image,twist,active,stages
def write_moves():
    rec=[move(i) for i in range(72)]
    S=['import Quadric.Five.Moves','','namespace Quadric.Five.Moves.Data',
       'set_option maxRecDepth 8192','set_option maxHeartbeats 8000000','set_option Elab.async false']
    for i,(image,twist,act,stages) in enumerate(rec):
        st=','.join(f'⟨{d},{hex(mask)}⟩' for d,mask in stages)
        S += [f'def m{i} : Move := ⟨{hex(image)},{hex(twist)},{hex(act)},[{st}]⟩',
              f'private theorem route{i} : routeOK m{i}=true := by decide +kernel']
    S+=['def table : List Move := ['+','.join('m'+str(i) for i in range(len(rec)))+']',
        'theorem table_routes : table.all routeOK=true := by',
        '  simp only [table,List.all_cons,List.all_nil,'+','.join('route'+str(i) for i in range(len(rec)))+',Bool.and_self]',
        'end Quadric.Five.Moves.Data']
    (OUT/'MoveData.lean').write_text('\n'.join(S)+'\n',encoding='utf8')
    from json import dumps
    from generate_claim_c_certificates import phase
    inner,outer=lines()
    # The submitted inner and outer catalogues both use lexicographic order in their
    # generator coordinates. The two equalities below recheck the order as well as signs.
    outer=sorted(outer,key=lambda l:(l[1],l[2]))
    inner=sorted(inner)
    geom=['import Quadric.Five.Resources.MoveData','import Quadric.Five.Catalogue','',
          'namespace Quadric.Five.Moves.Data','open Small Tagged',
          'set_option maxRecDepth 16384','set_option maxHeartbeats 16000000','set_option Elab.async false']
    for n,ls in [('insideLines',inner),('outerLines',outer)]:
        geom+=['noncomputable def '+n+' : List Line := signedLines% '+dumps(';'.join(','.join(map(str,l)) for l in ls))]
    geom+=['theorem inside_points : full3=insideLines := by decide +kernel',
           'theorem outer_points : outsideLines=outerLines := by',
           '  unfold outsideLines outsideLine isEdge; rw [←outside_coordinates]; decide +kernel',
           'end Quadric.Five.Moves.Data']
    (OUT/'MoveLines.lean').write_text('\n'.join(geom)+'\n',encoding='utf8')
    return rec
if __name__=='__main__':write_moves()
