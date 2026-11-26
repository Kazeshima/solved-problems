import Quadric.Five.PathRecords
import Quadric.Five.SurvivorCodes

namespace Quadric.Five.Moves
open Census

def CertifiedList (onH : Bool) (targets xs : List ℕ) : Prop :=
  ∀x∈xs,∃w : Witness,w.start=x ∧ w.target∈targets ∧ wordOK onH w=true

noncomputable def validRecord (onH : Bool) (targets : List ℕ) (w : Witness) :=
  targets.contains w.target && wordOK onH w

theorem certify_packet {onH : Bool} {targets xs : List ℕ} (ws : List Witness)
    (ids : ws.map Witness.start=xs) (valid : ws.all (validRecord onH targets)=true) :
    CertifiedList onH targets xs := by
  intro x hx
  rw [←ids] at hx
  obtain ⟨w,hw,e⟩:=List.mem_map.mp hx
  obtain ⟨t,v⟩:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid w hw)
  exact ⟨w,e,List.contains_iff_mem.mp t,v⟩

theorem CertifiedList.join {b : Bool} {ts l r : List ℕ} (x : CertifiedList b ts l) (y : CertifiedList b ts r) :
    CertifiedList b ts (l++r) := by
  intro a ha; exact (List.mem_append.mp ha).elim (x a) (y a)

theorem first_append (free : List ℕ) (start : ℕ) (xs ys : List (List ℕ)) :
    firstCodes free start (xs++ys)=firstCodes free start xs ++ firstCodes free (start+xs.length) ys := by
  induction xs generalizing start with
  | nil => simp [firstCodes]
  | cons r rs ih =>
    simp only [List.cons_append,firstCodes,List.length_cons,ih,List.append_assoc]
    rw [show start+1+rs.length=start+(rs.length+1) by omega]

theorem second_append (free : List ℕ) (rep start : ℕ) (xs ys : List Block.Row) :
    secondCodes free rep start (xs++ys)=secondCodes free rep start xs ++ secondCodes free rep (start+xs.length) ys := by
  induction xs generalizing start with
  | nil => simp [secondCodes]
  | cons r rs ih =>
    simp only [List.cons_append,secondCodes,List.length_cons,ih,List.append_assoc]
    rw [show start+1+rs.length=start+(rs.length+1) by omega]

end Quadric.Five.Moves
