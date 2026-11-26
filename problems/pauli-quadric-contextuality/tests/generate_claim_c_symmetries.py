"""Check signed elliptic automorphisms, and the deposited words selecting the canonical hyperplane."""
from pathlib import Path
from zipfile import ZipFile
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate_claim_c_certificates import ROOT, OUT
def generate():
    opts=['set_option maxRecDepth 16384','set_option maxHeartbeats 16000000','set_option Elab.async false']
    for group in range(12):
        head=['import Quadric.Five.MoveGeometry','','namespace Quadric.Five.Moves.Data',*opts]
        for i in range(6*group,6*group+6):
            head += [f'theorem geometry{i} : checkGeometry m{i}=true := by decide +kernel']
        head+=['end Quadric.Five.Moves.Data']
        (OUT/('Symmetry%02d.lean'%group)).write_text('\n'.join(head)+'\n',encoding='utf8')
    head=[f'import Quadric.Five.Resources.Symmetry{i:02d}' for i in range(12)]
    head+=['','namespace Quadric.Five.Moves.Data',*opts,'theorem all_good : ∀ m∈table,Good m := by',
           '  have all : table.all checkGeometry=true := by',
           '    simp only [table,List.all_cons,List.all_nil,'+','.join(f'geometry{i}' for i in range(72))+',Bool.and_self]',
           '  intro m hm; exact geometry_checked m (List.all_eq_true.mp table_routes m hm) (List.all_eq_true.mp all m hm)',
           'end Quadric.Five.Moves.Data']
    (OUT/'AllMoves.lean').write_text('\n'.join(head)+'\n',encoding='utf8')
    with ZipFile(ROOT/'sources/jonah-proof.zip') as z:
        ws=[x.split('\t') for x in z.read('CPL/data/point_words.tsv').decode().splitlines()]
    head=['import Quadric.Five.PointWords','import Quadric.Five.Resources.MoveLines','','namespace Quadric.Five.Moves.Data',
          'open Small',*opts,'def pointWords : List (List ℕ) := [[], '+', '.join('['+w+']' for _,w in ws)+']']
    assert [int(x) for x,w in ws]==list(range(1,64))
    head+=['def choiceFor (u : ℕ) := equalCatalogues ((hyperLines 36).map (backLine table (pointWords[u]?.getD []))) (hyperLines u)']
    for x,w in ws:
        head += [f'private theorem choice{x} : choiceFor {x}=true := by',
                 '  unfold choiceFor hyperLines; rw [inside_points]; decide +kernel']
    head+=['private theorem checked : hyperplanes.all choiceFor=true := by',
           '  rw [show hyperplanes='+str(list(range(1,64)))+' by decide +kernel]',
           '  simp only [List.all_cons,List.all_nil,'+','.join('choice'+x for x,w in ws)+',Bool.and_self]',
           'theorem transport_section (u : ℕ) (hu : u∈hyperplanes) (s : ℕ→Bool) :',
           '    hyperErrors (action table (pointWords[u]?.getD []) s) 36=hyperErrors s u :=',
           '  fix_section _ _ _ _ (List.all_eq_true.mp checked u hu)',
           'end Quadric.Five.Moves.Data']
    (OUT/'PointChoices.lean').write_text('\n'.join(head)+'\n',encoding='utf8')
if __name__=='__main__':generate()

