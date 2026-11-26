"""Recount distinct bounded solutions in the checkable census rows."""
from pathlib import Path
from zipfile import ZipFile
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import ROOT,OUT
from generate_claim_c_census import inst

opts=['set_option Elab.async false','set_option maxRecDepth 16384','set_option maxHeartbeats 16000000']
def main():
    front=['import Quadric.Five.CensusCounts','import Quadric.Five.Resources.LevelOne','namespace Quadric.Five.Census.LevelOne',*opts]
    for j in range(16):front += [f'private theorem unique{j} : chunk{j}.all (uniqueBelow 65536)=true := by decide +kernel']
    front+=['theorem all_bounded_unique : survivors.all (uniqueBelow 65536)=true := by',
            '  unfold survivors; simp only [List.all_append,'+','.join(f'unique{j}' for j in range(16))+',Bool.and_self]',
            'theorem distinct_survivors : (survivors.map (fun r=>r.toFinset.card)).sum=18752 :=',
            '  (count_distinct all_bounded_unique).trans lengths.2','end Quadric.Five.Census.LevelOne']
    (OUT/'FirstCount.lean').write_text('\n'.join(front)+'\n',encoding='utf8')
    counts=[]
    with ZipFile(ROOT/'sources/jonah-proof.zip') as z:
        for i in range(18):
            n=f'{i:02d}';_,_,_,_,xs=inst(z,i);counts.append(len(xs))
            ns='Quadric.Five.Census.Block.Case'+n
            groups={h:0 for h in range(0,2048,32)}
            for x in xs: groups[(x>>20)//32*32]+=1
            head=['import Quadric.Five.CensusCounts','import Quadric.Five.Resources.LevelTwo'+n,'namespace '+ns,*opts]
            for h,count in groups.items():
                head += [f'private theorem unique{h} : row{h}.all blockUnique=true := by decide +kernel',
                    f'private theorem count{h} : (row{h}.map rowCount).sum={count} := by decide +kernel']
            gp=[f'group{h}_{width}' for width in [64,128,256,512,1024,2048] for h in range(0,2048,width)]
            head+=['theorem bounded_unique : rows.all blockUnique=true := by',
                  '  simp only [rows,'+','.join(reversed(gp))+',List.all_append,'+','.join('unique'+str(h) for h in groups)+',Bool.and_self]',
                  f'theorem total_hits : (rows.map rowCount).sum={len(xs)} := by',
                  '  simp only [rows,'+','.join(reversed(gp))+',List.map_append,sum_join,'+','.join('count'+str(h) for h in groups)+',Nat.reduceAdd]',
                  'end '+ns]
            (OUT/('Count'+n+'.lean')).write_text('\n'.join(head)+'\n',encoding='utf8')
    code=['import Quadric.Five.Resources.FirstCount',*[f'import Quadric.Five.Resources.Count{i:02d}' for i in range(18)],'namespace Quadric.Five.Census',
        'theorem completion_census_count : ('+' + '.join(f'(Block.Case{i:02d}.rows.map rowCount).sum' for i in range(18))+')=34224 := by',
        '  rw ['+','.join(f'Block.Case{i:02d}.total_hits' for i in range(18))+']','end Quadric.Five.Census']
    code.pop()
    code+=['noncomputable def censusRows : List (List Block.Row) := ['+','.join(f'Block.Case{i:02d}.rows' for i in range(18))+']',
           'theorem unique_completions : censusRows.all (fun rs=>rs.all blockUnique)=true := by',
           '  simp only [censusRows,List.all_cons,List.all_nil,'+','.join(f'Block.Case{i:02d}.bounded_unique' for i in range(18))+',Bool.and_self]',
           'private theorem distinctSum (rs : List Block.Row) (hr : rs.all blockUnique=true) :',
           '    (rs.map distinctRowCount).sum=(rs.map rowCount).sum := by',
           '  congr 1; apply List.map_congr_left; intro r h; exact (row_distinct (List.all_eq_true.mp hr r h)).2',
           'theorem distinct_completion_count : (censusRows.map (fun rs=>(rs.map distinctRowCount).sum)).sum=34224 := by',
           '  have eq : censusRows.map (fun rs=>(rs.map distinctRowCount).sum)=censusRows.map (fun rs=>(rs.map rowCount).sum) := by',
           '    apply List.map_congr_left; intro rs hr; exact distinctSum rs (List.all_eq_true.mp unique_completions rs hr)',
           '  rw [eq]; simp only [censusRows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,'+','.join(f'Block.Case{i:02d}.total_hits' for i in range(18))+',Nat.reduceAdd]',
           'end Quadric.Five.Census']
    assert sum(counts)==34224
    (OUT/'CensusCount.lean').write_text('\n'.join(code)+'\n',encoding='utf8')
if __name__=='__main__':main()
