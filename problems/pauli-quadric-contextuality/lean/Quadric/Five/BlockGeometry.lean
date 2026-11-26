import Quadric.Five.OneBlock
import Quadric.Five.Coordinates
import Quadric.Five.Hyperplanes

namespace Quadric.Five.Census.Block
open Small

def splitForms (S : Split) :=
  (S.high.map fun u=>Affine.mk (shifted 20 11 u.1) u.2) ++ rawForms S.first 0 20 ++
    rawForms S.second 10 20 ++ rawForms S.crossBlock 10 0

def widths (S : Split) : Prop :=
  S.first.lowWidth=10 ∧ S.first.highWidth=11 ∧ S.second.lowWidth=10 ∧ S.second.highWidth=11 ∧
  S.crossBlock.lowWidth=10 ∧ S.crossBlock.highWidth=10

def sections := full3.filter (inHyperplane 36)
def crossing := full3.filter fun l=> !inHyperplane 36 l

theorem split_eval (S : Split) (w : widths S) (s : ℕ→Bool) :
    (splitForms S).countP (eval s)=fullCost S (field s 20 11) (field s 0 10) (field s 10 10) := by
  obtain ⟨a,b,c,d,e,f⟩:=w
  have h : (S.high.map (fun u=>Affine.mk (shifted 20 11 u.1) u.2)).countP (eval s) =
      highOnly S (field s 20 11) := by
    rw [List.countP_map]
    apply List.countP_congr; intro u hu; simp [eval,shifted_field,highOnly,Function.comp_def]
  simp only [splitForms,List.countP_append,h,system_geometry,a,b,c,d,e,f,fullCost]

theorem actual_cost (S : Split) (free : List ℕ) (rep : ℕ) (s : ℕ→Bool) (w : widths S)
    (eq : ((splitForms S).map normalized).Perm ((crossing.map (lineForm free rep)).map normalized)) :
    fullCost S (field s 20 11) (field s 0 10) (field s 10 10)=errors crossing (extendBits free rep s) := by
  rw [←split_eval S w]
  simpa only [List.countP_map,Function.comp_def,eval_normal,eval_line,errors] using eq.countP_eq (eval s)

theorem partition (s : ℕ→Bool) : errors full3 s=errors sections s+errors crossing s := by
  unfold errors sections crossing; generalize full3=ls
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases hh : inHyperplane 36 l <;> cases hf : Small.failure s l <;>
      simp [List.filter_cons,hh,hf,List.countP_cons,ih] <;> omega

def fixedSection (free : List ℕ) := sections.all fun l=>
  !free.contains l.a && !free.contains l.b && !free.contains l.c

theorem section_fixed (free : List ℕ) (rep : ℕ) (s : ℕ→Bool) (h : fixedSection free=true) :
    errors sections (extendBits free rep s)=errors sections rep.testBit := by
  unfold errors; apply List.countP_congr
  intro l hl
  have t:=List.all_eq_true.mp h l hl
  simp only [Bool.and_eq_true_iff,Bool.not_eq_true'] at t
  have no {p} (v : free.contains p=false) : p∉free := fun hp=>by
    have yes:=List.contains_iff_mem.mpr hp; rw [yes] at v; contradiction
  simp only [Small.failure,extend_at_fixed _ _ (no t.1.1),extend_at_fixed _ _ (no t.1.2),extend_at_fixed _ _ (no t.2)]

end Quadric.Five.Census.Block
