import Quadric.Five.PathRecords
import Quadric.Five.MoveBits

namespace Quadric.Five.Moves
open Small Tagged

/-- The two applications cancel the rephasing and transport the hyperplane indicator. -/
def keepsMask (m : Move) := (((inner m hyperMask ^^^ inner m 0) &&& hyperMask)==hyperMask)

private theorem from_mask (m : Move) (r : routeOK m=true) (ok : keepsMask m=true) : stable m=true := by
  apply List.all_eq_true.mpr; intro i hi
  have bound:=List.mem_range.mp hi
  change (!hyperMask.testBit i || hyperMask.testBit (source m i))=true
  cases bit:hyperMask.testBit i
  · simp
  · have eq:=congrArg (fun n:ℕ=>n.testBit i) (eq_of_beq ok)
    change (((inner m hyperMask ^^^ inner m 0) &&& hyperMask).testBit i)=hyperMask.testBit i at eq
    rw [Nat.testBit_and,Nat.testBit_xor,move_bit m hyperMask i r bound,move_bit m 0 i r bound,bit] at eq
    cases ph:m.twist.testBit i <;> cases he:hyperMask.testBit (source m i) <;> simp_all

private theorem stable_table : stableBits=packFlags (List.range 72)
    (fun i=>(Data.table[i]?.map keepsMask).getD false) := by decide +kernel

theorem stable_entry {i : ℕ} {m : Move} (h : isStable i=true) (hx : Data.table[i]?=some m) :
    stable m=true := by
  unfold isStable at h; rw [stable_table,flag_bit,hx] at h
  exact from_mask m (List.all_eq_true.mp Data.table_routes m (List.mem_of_getElem? hx))
    (Bool.and_eq_true_iff.mp h).2

end Quadric.Five.Moves
