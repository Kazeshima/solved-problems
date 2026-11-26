import Quadric.Five.LevelOneGeometry
import Quadric.Five.Deposit
import Quadric.Five.PathRecords
import Quadric.Five.SurvivorCodes

namespace Quadric.Five.Census.LevelOne
open Small Tagged Moves

def frameH : List ℕ := [1,2,8,9,16,36]
def maskH (s : ℕ→Bool) := carrier s &&& hyperMask

theorem free_shape : freePoints.Nodup ∧ freePoints.length=25 ∧
    freePoints.all (·<64)=true := by decide +kernel

private theorem splitH : (List.range 64).all (fun p=>
    hyperMask.testBit p == (freePoints.contains p || frameH.contains p))=true := by decide +kernel
private theorem lines_in_H : (full3.filter (inHyperplane 36)).all (fun l=>
    hyperMask.testBit l.a && hyperMask.testBit l.b && hyperMask.testBit l.c)=true := by decide +kernel

theorem hcode (s : ℕ→Bool) (fixed : ∀p∈frameH,s p=false) :
    maskH s=carrier (extendBits freePoints 0 (coordinates freePoints s)) := by
  apply Nat.eq_of_testBit_eq; intro p
  by_cases hi:p<64
  · unfold maskH; rw [Nat.testBit_and,carrier_at _ _ hi,carrier_at _ _ hi]
    have sh:=eq_of_beq (List.all_eq_true.mp splitH p (List.mem_range.mpr hi))
    rw [sh]
    by_cases hf:p∈freePoints
    · simp [hf,extend_at_free _ _ hf]
    · rw [extend_at_fixed _ _ hf]
      by_cases f:p∈frameH <;> simp [hf,f,fixed]
  · simp [maskH,Nat.testBit_and,carrier,flag_bit,hi]

theorem cost_normal (s : ℕ→Bool) (fixed : ∀p∈frameH,s p=false) :
    hyperErrors s 36=hyperErrors (extendBits freePoints 0 (coordinates freePoints s)) 36 := by
  unfold hyperErrors errors; apply List.countP_congr; intro l hl
  have here:=List.all_eq_true.mp lines_in_H l hl
  obtain ⟨ab,c⟩:=Bool.and_eq_true_iff.mp here
  obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp ab
  have bit (p) (hp:hyperMask.testBit p=true) :
      s p=extendBits freePoints 0 (coordinates freePoints s) p := by
    have lt:p<64 := by
      by_contra! hn
      have z:=Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : hyperMask<2^64) (Nat.pow_le_pow_right (by decide) hn))
      rw [z] at hp; contradiction
    have e:=congrArg (fun x:ℕ=>x.testBit p) (hcode s fixed)
    simpa only [maskH,Nat.testBit_and,hp,Bool.and_true,carrier_at _ _ lt] using e
  simp only [Small.failure,bit _ a,bit _ b,bit _ c]

theorem normalized_in_census (s : ℕ→Bool) (fixed : ∀p∈frameH,s p=false)
    (cheap : hyperErrors s 36≤21) :
    maskH s∈firstCodes freePoints 0 survivors := by
  let c:=coordinates freePoints s
  have z:=cheap; rw [cost_normal s fixed] at z
  have mem:=(section_census c).mp z
  have hh:=field_lt c 16 9
  have hit:=first_mem freePoints 0 survivors (field c 16 9) (field c 0 16)
    (by rw [lengths.1]; exact hh) mem
  have dep:expand freePoints 0 (field c 0 freePoints.length)=deposit freePoints (field c 0 freePoints.length) := by
    simpa using expand_eq freePoints free_shape.1 0 _ (by simp) (by decide) (fun p hp=>
      of_decide_eq_true (List.all_eq_true.mp free_shape.2.2 p hp))
  rw [hcode s fixed,←expand_field,dep,free_shape.2.1]
  rw [show (25:ℕ)=16+9 by decide,field_concat c 0 16 9]
  simpa using hit

end Quadric.Five.Census.LevelOne
