import Quadric.Five.CensusReach
import Quadric.Five.Frame
import Quadric.Five.RestrictWords

namespace Quadric.Five.Moves
open Small Tagged Data
def repairWord (z r : Bool) : List ℕ := (if r then [66,69] else []) ++ (if z then [71] else [])

private def repairOK (z r : Bool) :=
  let w:=repairWord z r
  let d:=walk table w 0
  w.all diagonalIndex && (d &&& hyperMask)==0 && d.testBit 0==z && d.testBit 4==r

private theorem repair_ok (z r : Bool) : repairOK z r=true := by cases z <;> cases r <;> decide +kernel

theorem repair (good : ∀m∈table,Good m) (s : ℕ→Bool) : ∃t:ℕ→Bool,
    agrees (carrier t) (carrier s) ∧ t 0=false ∧ t 4=false ∧
    errors full3 t=errors full3 s ∧ errors ellipticLines t=errors ellipticLines s ∧ Reach table s t := by
  let x:=carrier s
  let w:=repairWord (x.testBit 0) (x.testBit 4)
  let d:=walk table w 0
  have ck:=repair_ok (x.testBit 0) (x.testBit 4)
  change (((w.all diagonalIndex && ((d &&& hyperMask)==0)) && d.testBit 0==x.testBit 0) && d.testBit 4==x.testBit 4)=true at ck
  simp only [Bool.and_eq_true_iff,beq_iff_eq] at ck
  obtain ⟨⟨⟨diag,ms⟩,z⟩,r⟩:=ck
  let t:=action table w s
  obtain ⟨sig,hs,ha⟩:=travel table good w s
  have bit (i) (hi:i<64) : t i=(x.testBit i ^^ d.testBit i) := by
    rw [←carrier_at t i hi]; exact (congrArg (fun v:ℕ=>v.testBit i) sig).trans (diagonal_word w diag x i hi)
  refine ⟨t,?_,by rw [bit 0 (by decide),z]; simp,by rw [bit 4 (by decide),r]; simp,hs,ha,⟨w,rfl⟩⟩
  apply (agree_bits ..).mpr; intro i hi
  have lt : i<64 := by
    by_contra! b
    have h:=Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : hyperMask<2^64) (Nat.pow_le_pow_right (by decide) b))
    rw [h] at hi; contradiction
  have b:=congrArg (fun v:ℕ=>v.testBit i) ms
  have no : d.testBit i=false := by simpa only [Nat.testBit_and,hi,Bool.and_true,Nat.zero_testBit] using b
  rw [carrier_at _ _ lt,bit i lt,no,Bool.xor_false]

end Quadric.Five.Moves
