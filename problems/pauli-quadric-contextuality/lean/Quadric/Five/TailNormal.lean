import Quadric.Five.SurvivorCodes
import Quadric.Five.PathRecords

namespace Quadric.Five.Census
open Small Tagged Moves Block
def tailFree : List ℕ := [5,6,7,12,13,14,15,20,21,22,23,28,29,30,31,32,33,34,35,40,41,42,43,48,49,50,51,56,57,58,59]
private theorem tail_shape : tailFree.length=31 ∧ tailFree.Nodup ∧ tailFree.all (·<64)=true := by decide +kernel
private theorem partition_bits : (List.range 64).all (fun p=>tailFree.contains p ==
    (!hyperMask.testBit p && p != 0 && p != 4))=true := by decide +kernel
private theorem bounded_lines : full3.all (fun l=>l.a<64 && l.b<64 && l.c<64)=true := by decide +kernel

def Masked (s : ℕ→Bool) (rep : ℕ) := carrier s &&& hyperMask = rep
private theorem masked_bit {s : ℕ→Bool} {rep : ℕ} (h : Masked s rep) {p : ℕ} (hp:p<64) :
    (s p && hyperMask.testBit p)=rep.testBit p := by
  have e:=congrArg (fun x:ℕ=>x.testBit p) h
  simpa only [Nat.testBit_and,carrier_at _ _ hp] using e

theorem signature_fixed (s : ℕ→Bool) (rep : ℕ) (mask : Masked s rep)
    (zero : s 0=false) (r0 : s 4=false) {p : ℕ} (hp:p<64) (nf:p∉tailFree) : s p=rep.testBit p := by
  have eq:=masked_bit mask hp
  cases h:hyperMask.testBit p
  · have part:=eq_of_beq (List.all_eq_true.mp partition_bits p (List.mem_range.mpr hp))
    have cases : p=0 ∨ p=4 := by
      by_contra! hn
      simp [h,nf,hn.1,hn.2] at part
    rcases cases with rfl|rfl <;> simp_all
  · simpa [h] using eq

theorem extension_exact (s : ℕ→Bool) (rep : ℕ) (mask : Masked s rep)
    (zero : s 0=false) (r0 : s 4=false) {p : ℕ} (hp:p<64) :
    extendBits tailFree rep (coordinates tailFree s) p=s p := by
  by_cases hf:p∈tailFree
  · exact extend_at_free _ _ hf
  · rw [extend_at_fixed _ _ hf]; exact (signature_fixed s rep mask zero r0 hp hf).symm

theorem extension_errors (s : ℕ→Bool) (rep : ℕ) (mask : Masked s rep)
    (zero : s 0=false) (r0 : s 4=false) :
    errors full3 (extendBits tailFree rep (coordinates tailFree s))=errors full3 s := by
  unfold errors; apply List.countP_congr; intro l hl
  have hh:=List.all_eq_true.mp bounded_lines l hl
  simp only [Bool.and_eq_true_iff,decide_eq_true_eq] at hh
  simp only [Small.failure,extension_exact s rep mask zero r0 hh.1.1,
    extension_exact s rep mask zero r0 hh.1.2,extension_exact s rep mask zero r0 hh.2]

def CompleteBlock (rep : ℕ) (rows : List Block.Row) (len : rows.length=2048) : Prop :=
  ∀ c : ℕ→Bool, errors full3 (extendBits tailFree rep c)≤92 →
    member (rows[field c 20 11]'(len.symm ▸ field_lt c 20 11)) (field c 0 10) (field c 10 10)

theorem completion_in_codes (s : ℕ→Bool) (rep : ℕ) (mask : Masked s rep)
    (zero : s 0=false) (r0 : s 4=false) (low : errors full3 s≤92)
    (rows : List Block.Row) (len : rows.length=2048) (ready : CompleteBlock rep rows len) :
    carrier s∈secondCodes tailFree rep 0 rows := by
  let c:=coordinates tailFree s
  have good:=ready c (by rwa [extension_errors s rep mask zero r0])
  have hit:=second_mem tailFree rep 0 rows (field c 20 11) (field c 0 10) (field c 10 10)
    (len.symm ▸ field_lt c 20 11) good
  have same : carrier s = carrier (extendBits tailFree rep c) := by
    apply Nat.eq_of_testBit_eq; intro p
    by_cases hp:p<64
    · rw [carrier_at _ _ hp,carrier_at _ _ hp,extension_exact s rep mask zero r0 hp]
    · simp [carrier,flag_bit,hp]
  have lim : rep<2^64 := by
    rw [←mask]; exact lt_of_le_of_lt Nat.and_le_right (by decide : hyperMask<2^64)
  have dis (p) (hp:p∈tailFree) : rep.testBit p=false := by
    have lt:=of_decide_eq_true (List.all_eq_true.mp tail_shape.2.2 _ hp)
    have part:=eq_of_beq (List.all_eq_true.mp partition_bits p (List.mem_range.mpr lt))
    have off : hyperMask.testBit p=false := by cases h:hyperMask.testBit p <;> simp_all
    simpa [off] using (masked_bit mask lt).symm
  rw [same,←expand_field,expand_eq tailFree tail_shape.2.1 _ _ dis lim
    (fun _ h=>of_decide_eq_true (List.all_eq_true.mp tail_shape.2.2 _ h)),tail_shape.1]
  rw [show (31:ℕ)=20+11 by decide,field_concat c 0 20 11,
    show (20:ℕ)=10+10 by decide,field_concat c 0 10 10]
  simpa only [Nat.zero_add,Nat.add_assoc] using hit

end Quadric.Five.Census
