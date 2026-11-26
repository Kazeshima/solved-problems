import Quadric.Five.PathData
import Quadric.Five.MoveBits

namespace Quadric.Five.Moves
open Small Tagged

def agrees (x y : ℕ) := (x &&& hyperMask)=(y &&& hyperMask)
theorem agree_bits (x y : ℕ) :
    agrees x y ↔ ∀ i, hyperMask.testBit i=true → x.testBit i=y.testBit i := by
  constructor
  · intro h i hi
    have eq:=congrArg (fun z:ℕ=>z.testBit i) h
    simpa only [Nat.testBit_and,hi,Bool.and_true] using eq
  · intro h; apply Nat.eq_of_testBit_eq; intro i
    cases he:hyperMask.testBit i <;> simp [Nat.testBit_and,he,h i]

private theorem hbit_lt {i : ℕ} (h : hyperMask.testBit i=true) : i<64 := by
  by_contra! hn
  have hi : hyperMask < 2^i := lt_of_lt_of_le (by decide : hyperMask<2^64) (Nat.pow_le_pow_right (by decide) hn)
  rw [Nat.testBit_lt_two_pow hi] at h; contradiction

theorem step_agrees {m : Move} {x y : ℕ} (r : routeOK m=true) (st : stable m=true)
    (eq : agrees x y) : agrees (inner m x) (inner m y) := by
  apply (agree_bits ..).mpr; intro i hi
  have lt:=hbit_lt hi
  have here:=List.all_eq_true.mp st i (List.mem_range.mpr lt)
  have there : hyperMask.testBit (source m i)=true := by simpa [hi] using here
  rw [move_bit _ _ _ r lt,move_bit _ _ _ r lt,(agree_bits ..).mp eq _ there]

theorem walk_agrees (w : List ℕ) {x y : ℕ} (hw : w.all isStable=true) (h : agrees x y) :
    agrees (walk Data.table w x) (walk Data.table w y) := by
  induction w generalizing x y with
  | nil => exact h
  | cons i w ih =>
    obtain ⟨head,tail⟩:=Bool.and_eq_true_iff.mp hw
    cases e:Data.table[i]? with
    | none => simpa only [walk,e] using ih tail h
    | some m =>
      have r:=List.all_eq_true.mp Data.table_routes m (List.mem_of_getElem? e)
      simpa only [walk,e] using ih tail (step_agrees r (stable_entry head e) h)

end Quadric.Five.Moves
