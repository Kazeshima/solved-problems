"""Assemble the checked census rows and orbit packets into the two coverage theorems."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import OUT

opts=['set_option maxRecDepth 16384','set_option maxHeartbeats 12000000','set_option Elab.async false']
def write(name,src):
    (OUT/(name+'.lean')).write_text('\n'.join(src)+'\n',encoding='utf8')
def generate():
    H=['import Quadric.Five.Family',*[f'import Quadric.Five.Resources.HBridge{i:02d}' for i in range(16)],
       'namespace Quadric.Five.Moves.Data','open Census',*opts]
    for i in reversed(range(16)):
        chunk=f'LevelOne.chunk{i}';h=32*i;leaf=f'HPacket{i:02d}.cover{h}'
        H+=[f'private noncomputable def tail{i} := '+(chunk if i==15 else chunk+f' ++ tail{i+1}'),
            f'private theorem accepted{i} : CertifiedList true hProfiles (firstCodes LevelOne.freePoints {h} tail{i}) :=']
        if i==15:H+=['  '+leaf]
        else:H += [f'  @jointFirst hProfiles LevelOne.freePoints {h} 32 {chunk} tail{i+1} (by decide +kernel) {leaf} accepted{i+1}']
    H+=['theorem hyperplane_census : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 0 LevelOne.survivors) := accepted0','end Quadric.Five.Moves.Data']
    write('AllHyperplanes',H)
    for i in range(18):
        nn=f'{i:02d}';ns='Quadric.Five.Census.Block.Case'+nn
        C=['import Quadric.Five.Family','import Quadric.Five.Resources.CaseForms'+nn,
           *[f'import Quadric.Five.Resources.RBridge{nn}_{j}' for j in range(4)],
           'namespace '+ns,'open Quadric.Five.Moves Quadric.Five.Moves.Data',*opts]
        parts=[(f'row{h}',f'RPacket{nn}_{h//512}.cover{h}',h,32) for h in range(0,2048,32)]
        while len(parts)>1:
            new=[]
            for j in range(0,len(parts),2):
                l,p,h,n=parts[j];r,q,k,m=parts[j+1];name=f'group{h}_{n+m}';pr='cover'+name
                C += [f'private theorem {pr} : CertifiedList false fullProfiles (secondCodes freePoints restriction {h} {name}) :=',
                    f'  @jointSecond fullProfiles freePoints restriction {h} {n} {l} {r} (by decide +kernel) {p} {q}']
                new.append((name,pr,h,n+m))
            parts=new
        C += ['theorem profile_case : ProfileCase restriction := by',
              '  have names : freePoints=tailFree := by decide +kernel',
              '  refine ⟨rows,rows_length,?_,?_⟩',
              '  · intro c low',
              '    have bound := (threshold_iff c).mp (by simpa only [names] using low)',
              '    exact (coverage _ _ _ (field_lt ..) (field_lt ..) (field_lt ..)).mp (by simpa only [Nat.zero_add] using bound)',
              '  · simpa only [names] using '+parts[0][1],
              'end '+ns]
        write('CloseCase'+nn,C)
    C=[*[f'import Quadric.Five.Resources.CloseCase{i:02d}' for i in range(18)],
       'namespace Quadric.Five.Moves.Data','open Census',*opts,
       'private def AllProfiles : List ℕ→Prop | []=>True | x::xs=>ProfileCase x ∧ AllProfiles xs',
       'private theorem all_profiles : AllProfiles hProfiles :=',
       '  ⟨'+', '.join(f'Block.Case{i:02d}.profile_case' for i in range(18))+', trivial⟩',
       'theorem complete_cases : ∀x∈hProfiles,ProfileCase x := by',
       '  have elim (xs : List ℕ) (h : AllProfiles xs) : ∀ x∈xs,ProfileCase x := by',
       '    induction xs with',
       '    | nil => simp',
       '    | cons a xs ih => intro x hx; rcases List.mem_cons.mp hx with rfl|hz; exact h.1; exact ih h.2 x hz',
       '  exact elim _ all_profiles','end Quadric.Five.Moves.Data']
    write('AllCases',C)
if __name__=='__main__':generate()
