import Quadric.Five.Resources.FrameChoices
import Quadric.Five.Resources.MoveLines
import Quadric.Five.PointWords
import Quadric.Five.CensusReach

namespace Quadric.Five.Moves
open Small Tagged Data
noncomputable def cachedH := insideLines.filter (inHyperplane 36)
theorem cache_h : hyperLines 36 = cachedH := by unfold hyperLines cachedH; rw [inside_points]

noncomputable def gaugeCheck (i : ℕ) :=
  equalCatalogues (cachedH.map (backLine table [i])) cachedH

theorem gauge_preserves_h {i : ℕ} (lb:64 ≤ i) (ub:i<72) (s : ℕ→Bool)
    (checks : (List.range' 64 8).all gaugeCheck=true) :
    hyperErrors (action table [i] s) 36=hyperErrors s 36 := by
  apply fix_section
  rw [cache_h]
  apply List.all_eq_true.mp checks
  simp [List.mem_range']; exact ⟨i-64,by omega,by omega⟩

theorem gauges_preserve (w : List ℕ) (hw : onlyGauges w=true)
    (checks : (List.range' 64 8).all gaugeCheck=true) (s : ℕ→Bool) :
    hyperErrors (action table w s) 36=hyperErrors s 36 := by
  induction w generalizing s with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨one,rest⟩:=Bool.and_eq_true_iff.mp hw
    obtain ⟨lo,hi⟩:=Bool.and_eq_true_iff.mp one
    have step:=gauge_preserves_h (of_decide_eq_true lo) (of_decide_eq_true hi) s checks
    cases e:table[i]? with
    | none=> simpa only [action,e] using ih rest s
    | some m=>
      simpa only [action,e] using (ih rest (pull m s)).trans (by simpa only [action,e] using step)

theorem normalize_frame (good : ∀m∈table,Good m) (checks : (List.range' 64 8).all gaugeCheck=true)
    (s : ℕ→Bool) : ∃ t : ℕ→Bool, (∀p∈frame,t p=false) ∧
      hyperErrors t 36=hyperErrors s 36 ∧ errors full3 t=errors full3 s ∧ errors ellipticLines t=errors ellipticLines s ∧ Reach table s t := by
  let w:=choice (keyBits (carrier s) frame)
  obtain ⟨fc,gc⟩:=choice_valid (carrier s)
  obtain ⟨sig,hs,he⟩:=travel table good w s
  refine ⟨action table w s,?_,gauges_preserve w gc checks s,hs,he,⟨w,rfl⟩⟩
  intro p hp
  have lt:= of_decide_eq_true (List.all_eq_true.mp (by decide : frame.all (·<64)=true) p hp)
  rw [←carrier_at (action table w s) p lt,sig]
  exact zeros_after _ w fc _ hp

end Quadric.Five.Moves
