import Quadric.Five.Moves

namespace Quadric.Five.Moves
open Small Tagged
theorem move_bit (m : Move) (x i : ℕ) (hm : routeOK m=true) (hi : i<64) :
    (inner m x).testBit i = (x.testBit (source m i) ^^ m.twist.testBit i) := by
  obtain ⟨shape,src⟩:=Bool.and_eq_true_iff.mp hm
  have eq:=eq_of_beq (List.all_eq_true.mp src i (List.mem_range.mpr hi))
  have hh:=permute_at m.stages x i shape hi
  simp only [inner,Nat.testBit_mod_two_pow,hi,decide_true,Bool.true_and,Nat.testBit_xor,
    Nat.testBit_and,hh.1,eq]
  cases b:m.active.testBit i <;> simp [b]


end Quadric.Five.Moves
