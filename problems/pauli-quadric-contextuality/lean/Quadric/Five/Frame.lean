import Quadric.Five.Paths
import Quadric.Five.PointWords
import Quadric.Five.Resources.MoveLines

namespace Quadric.Five.Moves
open Small Tagged
def frame : List ℕ := [1,2,8,9,16,36,4,0]

def diagonalIndex (i : ℕ) :=
  match Data.table[i]? with
  | none=>true
  | some m=>m.active == 0

private theorem mask_at (m : Move) (x i : ℕ) (h : m.active=0) (hi:i<64) :
    (inner m x).testBit i=(x.testBit i ^^ m.twist.testBit i) := by
  unfold inner; simp only [h,Nat.and_zero,Nat.zero_xor,Nat.testBit_mod_two_pow,hi,decide_true,Bool.true_and,Nat.testBit_xor]

theorem diagonal_word (w : List ℕ) (hw : w.all diagonalIndex=true) (x i : ℕ) (hi:i<64) :
    (walk Data.table w x).testBit i=(x.testBit i ^^ (walk Data.table w 0).testBit i) := by
  induction w generalizing x with
  | nil => simp [walk]
  | cons k ks ih =>
    obtain ⟨h,t⟩:=Bool.and_eq_true_iff.mp hw
    cases e:Data.table[k]? with
    | none => simpa only [walk,e] using ih t x
    | some m =>
      have zero : m.active=0 := by simpa [diagonalIndex,e] using h
      simp only [walk,e,ih t (inner m x),ih t (inner m 0),mask_at m _ _ zero hi,Nat.zero_testBit,Bool.false_xor,Bool.xor_assoc]

theorem keyBits_lt (x : ℕ) (ps : List ℕ) : keyBits x ps < 2^ps.length := by
  induction ps with
  | nil => simp [keyBits]
  | cons p ps ih =>
    rw [keyBits,List.length_cons,pow_succ]
    cases x.testBit p <;> simp <;> omega

theorem key_agreement {x y : ℕ} {ps : List ℕ} (h : keyBits x ps=keyBits y ps) :
    ∀p∈ps,x.testBit p=y.testBit p := by
  induction ps with
  | nil => simp
  | cons k ks ih =>
    simp only [keyBits] at h
    have vals : x.testBit k=y.testBit k ∧ keyBits x ks=keyBits y ks := by
      cases he:x.testBit k <;> cases hh:y.testBit k <;> simp_all <;> omega
    intro p hp; rcases List.mem_cons.mp hp with rfl|hp
    · exact vals.1
    · exact ih vals.2 p hp

def frameCheck (k : ℕ) (w : List ℕ) := w.all diagonalIndex && keyBits (walk Data.table w 0) frame == k

theorem zeros_after (x : ℕ) (w : List ℕ) (h : frameCheck (keyBits x frame) w=true) :
    ∀p∈frame,(walk Data.table w x).testBit p=false := by
  obtain ⟨diag,keys⟩:=Bool.and_eq_true_iff.mp h
  intro p hp
  have lt : p<64 := of_decide_eq_true (List.all_eq_true.mp (by decide : frame.all (·<64)=true) p hp)
  rw [diagonal_word w diag x p lt,key_agreement (eq_of_beq keys) p hp]
  simp

end Quadric.Five.Moves
