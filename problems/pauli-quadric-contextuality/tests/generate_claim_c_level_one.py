"""Generate the exact 25-coordinate hyperplane system and its proposed complete survivor list."""
import json, sys
from pathlib import Path
from zipfile import ZipFile
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_census import syslit, ROOT
from generate_claim_c_certificates import sym, phase

OUT=ROOT/"lean/Quadric/Five/Resources/LevelOne.lean"
def generate():
    H=[p for p in range(1,64) if not sym(3,36,p)]
    vs=[p for p in H if p not in (1,2,8,9,16,36)]
    assert len(vs)==25
    bit=lambda p: 1<<vs.index(p) if p in vs else 0
    ls=[(p,q,p^q,phase(3,p,q)//2) for p in H for q in H if p<q<p^q and
        p^q in H and not sym(3,p,q)]
    assert len(ls)==75
    fs=[(bit(p)^bit(q)^bit(t),s) for p,q,t,s in ls]
    with ZipFile(ROOT/'sources/jonah-proof.zip') as z:
        sig=[int(x,16) for x in z.read('CPL/data/level1_list.txt').splitlines()]
    assert len(set(sig))==18752
    k=16
    rows=[[] for _ in range(1<<(25-k))]
    for x in sig:
        w=sum((x>>p&1)<<j for j,p in enumerate(vs))
        assert x==sum((w>>j&1)<<p for j,p in enumerate(vs))
        rows[w>>k].append(w%2**k)
    src=['import Quadric.Five.Append','import Quadric.Five.Literals','',
       'namespace Quadric.Five.Census.LevelOne','set_option maxRecDepth 16384',
       'set_option maxHeartbeats 20000000','set_option Elab.async false',
       'noncomputable def system : System := '+syslit(fs,k,25-k,21),
       'def freePoints : List ℕ := '+str(vs),
       'theorem systemSize : size system=75 := by decide +kernel']
    parts=[]
    for a in range(0,len(rows),32):
        x=rows[a:a+32]
        nm='chunk'+str(a//32)
        raw=';'.join(','.join(map(str,sorted(y))) for y in x)
        src+=['noncomputable def '+nm+' : List (List ℕ) := natRows% '+json.dumps(raw),
          'private theorem checked'+str(a//32)+' : rowsOK system '+str(a)+' '+nm+'=true := by decide +kernel']
        parts.append(nm)
    src+=['noncomputable def survivors := '+' ++ '.join(parts),
          'theorem census : rowsOK system 0 survivors=true := by',
          '  unfold survivors rowsOK',
          '  simp only [checkRows_append]']
    names=['checked'+str(j) for j in range(len(parts))]
    src+=['  change '+' && '.join('rowsOK system '+str(32*j)+' '+nm for j,nm in enumerate(parts))+'=true',
          '  rw ['+','.join(names)+']','  rfl',
          'theorem lengths : survivors.length=512 ∧ (survivors.map List.length).sum=18752 := by decide +kernel',
          'theorem coverage (h l : ℕ) (hh : h<512) (hl : l<65536) :',
          '    errorCount system h l≤21 ↔ l∈survivors[h]\'(lengths.1.symm ▸ hh) := by',
          '  simpa using rows_sound system (by rw [systemSize]; decide) (by decide) 0 survivors census h l (by simpa only [lengths.1] using hh) hl',
          'end Quadric.Five.Census.LevelOne']
    return '\n'.join(src)+'\n'
if __name__=='__main__':
    OUT.write_text(generate(),encoding='utf8')
