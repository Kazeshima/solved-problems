import Quadric.Five.Coordinates

namespace Quadric.Five.Census
open Tagged

def deposit : List ℕ→ℕ→ℕ
  | [],_=>0
  | p::ps,x=>(if x.testBit 0 then 2^p else 0) ||| deposit ps (x>>>1)

theorem deposited_bit (free : List ℕ) (nd : free.Nodup) (w p : ℕ) :
    (deposit free w).testBit p = (decide (p∈free) && w.testBit (free.idxOf p)) := by
  induction free generalizing w with
  | nil => simp [deposit]
  | cons a xs ih =>
    obtain ⟨ha,pair⟩:=List.nodup_cons.mp nd
    rw [deposit,Nat.testBit_or,ih pair]
    by_cases hp:p=a
    · subst p; cases h:w.testBit 0 <;> simp [h,ha,Nat.testBit_two_pow]
    · cases h:w.testBit 0 <;> simp [List.idxOf_cons,Ne.symm hp,h,hp,Nat.testBit_two_pow,Nat.testBit_shiftRight,Nat.add_comm]

theorem expand_eq (free : List ℕ) (nd : free.Nodup) (rep w : ℕ)
    (dis : ∀p∈free,rep.testBit p=false) (lim : rep<2^64) (small : ∀p∈free,p<64) :
    expand free rep w=rep ||| deposit free w := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_or,deposited_bit free nd]
  by_cases hi:p<64
  · unfold expand; rw [carrier_at _ _ hi]
    by_cases hf:p∈free
    · simp [extendBits,eval,pointForm,hf,dis p hf,foldBits]
    · simp [extend_at_fixed _ _ hf,hf]
  · have hrep:=Nat.testBit_lt_two_pow (lim.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))
    have no : p∉free:=fun he=>hi (small p he)
    simp [expand,carrier,flag_bit,hi,no,hrep]

end Quadric.Five.Census
