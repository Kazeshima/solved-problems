"""Tabulate the seven physical gauge coefficients and the auxiliary bit-zero normalization."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import OUT
from generate_claim_c_paths import setup,step
ps=[1,2,8,9,16,36,4,0]
def write():
    moves,_,_=setup();words=[None]*256
    for sel in range(256):
        w=[64+j for j in range(8) if sel>>j&1];x=0
        for i in w:x=step(moves[i],x)
        key=sum((x>>p&1)<<j for j,p in enumerate(ps))
        assert words[key] is None
        words[key]=w
    assert all(w is not None for w in words)
    src=['import Quadric.Five.Frame','','namespace Quadric.Five.Moves.Data','open Small Tagged',
         'set_option maxHeartbeats 12000000','set_option maxRecDepth 8192','set_option Elab.async false',
         'def adjustments : List (List ℕ) := '+str(words),
         'def choice (i : ℕ) := adjustments[i]?.getD []',
         'def onlyGauges (w : List ℕ) := w.all (fun i=>64 ≤ i && i<72)']
    for start in range(0,256,16):
        src+=['private theorem packet'+str(start)+' : (List.range\' '+str(start)+' 16).all (fun i=>frameCheck i (choice i) && onlyGauges (choice i))=true := by decide +kernel']
    src+=['private theorem all_choices : (List.range 256).all (fun i=>frameCheck i (choice i) && onlyGauges (choice i))=true := by',
          '  rw [show List.range 256='+' ++ '.join('(List.range\' '+str(i)+' 16)' for i in range(0,256,16))+' by decide +kernel]',
          '  simp only [List.all_append,'+','.join('packet'+str(i) for i in range(0,256,16))+',Bool.and_self]',
          'theorem choice_valid (x : ℕ) : frameCheck (keyBits x frame) (choice (keyBits x frame))=true ∧ onlyGauges (choice (keyBits x frame))=true := by',
          '  apply Bool.and_eq_true_iff.mp; apply List.all_eq_true.mp all_choices',
          '  exact List.mem_range.mpr (by simpa [frame] using keyBits_lt x frame)',
          'end Quadric.Five.Moves.Data']
    (OUT/'FrameChoices.lean').write_text('\n'.join(src)+'\n',encoding='utf8')
if __name__=='__main__': write()
