import Quadric.Five.CensusSemantics

namespace Quadric.Five.Census
open Tagged Small

theorem field_concat (s : ℕ→Bool) (o n m : ℕ) :
    field s o (n+m)=2^n*field s (o+n) m+field s o n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_two_pow_mul_add _ (field_lt s o n),field_at]
  by_cases lo:i<n
  · have whole : i<n+m:=by omega
    simp [lo,whole,field_at]
  · have eq : o+n+(i-n)=o+i := by omega
    by_cases b:i<n+m
    · have yes : i-n<m:=by omega
      simp [lo,b,field_at,yes,eq]
    · have no : ¬i-n<m:=by omega
      simp [lo,b,field_at,no]

def coordinates (free : List ℕ) (s : ℕ→Bool) (j : ℕ) := s (free[j]?.getD 0)

theorem extend_at_free {free : List ℕ} (rep : ℕ) (s : ℕ→Bool) {p : ℕ} (hp : p∈free) :
    extendBits free rep (coordinates free s) p = s p := by
  have h:=List.idxOf_lt_length hp
  simp [extendBits,eval,pointForm,hp,foldBits,coordinates,List.getElem?_eq_getElem h,List.getElem_idxOf h]

theorem extend_at_fixed {free : List ℕ} (rep : ℕ) (s : ℕ→Bool) {p : ℕ} (hp : p∉free) :
    extendBits free rep s p=rep.testBit p := by simp [extendBits,eval,pointForm,hp,foldBits]

/-- Convert a free-coordinate integer to its physical three-qubit labels. -/
def expand (free : List ℕ) (rep w : ℕ) := carrier (extendBits free rep w.testBit)

theorem expand_field (free : List ℕ) (rep : ℕ) (s : ℕ→Bool) :
    expand free rep (field s 0 free.length)=carrier (extendBits free rep s) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i<64
  · unfold expand; rw [carrier_at _ _ hi,carrier_at _ _ hi]
    by_cases he:i∈free
    · have lt:=List.idxOf_lt_length he
      simp [extendBits,eval,pointForm,he,foldBits,field_at,lt]
    · simp [extend_at_fixed _ _ he]
  · simp [expand,carrier,flag_bit,hi]

theorem reconstruct (free : List ℕ) (rep : ℕ) (s : ℕ→Bool)
    (fixed : ∀p<64,p∉free → s p=rep.testBit p) :
    carrier s=expand free rep (field (coordinates free s) 0 free.length) := by
  rw [expand_field]; apply Nat.eq_of_testBit_eq; intro i
  by_cases hi:i<64
  · rw [carrier_at _ _ hi,carrier_at _ _ hi]
    by_cases he:i∈free
    · exact (extend_at_free rep s he).symm
    · rw [extend_at_fixed _ _ he]; exact fixed i hi he
  · simp [carrier,flag_bit,hi]

end Quadric.Five.Census
