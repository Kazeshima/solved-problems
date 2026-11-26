import Quadric.Five.FramePhysics
import Quadric.Five.Repair
import Quadric.Five.HyperplaneNormal
import Quadric.Five.Family
import Quadric.Five.Packets
import Quadric.Five.Resources.ProfileMasks
import Quadric.Five.Resources.PointChoices
import Quadric.Five.Resources.HyperplaneData

namespace Quadric.Five.Moves
open Small Tagged Data Census

theorem classification_to_bounds (good : ∀m∈Data.table,Good m)
    (gauges : (List.range' 64 8).all gaugeCheck=true)
    (hyper : CertifiedList true hProfiles (firstCodes LevelOne.freePoints 0 LevelOne.survivors))
    (perProfile : ∀rep∈hProfiles,ProfileCase rep)
    (s : ℕ→Bool) (low : errors full3 s≤92) :
    ∃ t : ℕ→Bool, carrier t∈fullProfiles ∧ errors ellipticLines t=errors ellipticLines s ∧ Reach Data.table s t := by
  obtain ⟨u,hu,cheap⟩:=HyperplaneData.low_section low
  let w:=pointWords[u]?.getD []
  let s₁:=action Data.table w s
  have ht:=travel Data.table good w s
  have hc : hyperErrors s₁ 36≤21 := (transport_section u hu s).le.trans cheap
  obtain ⟨s₂,zeros,hc₂,w₂,e₂,reach₂⟩:=normalize_frame good gauges s₁
  have hcF : LevelOne.frameH.all (frame.contains ·)=true := by decide +kernel
  have sub : ∀p∈LevelOne.frameH,p∈frame := fun p hp=>List.contains_iff_mem.mp (List.all_eq_true.mp hcF p hp)
  have ind:=LevelOne.normalized_in_census s₂ (fun p hp=>zeros p (sub p hp)) (hc₂.le.trans hc)
  obtain ⟨alpha,firstSig,target,checked⟩:=hyper _ ind
  let s₃:=action Data.table alpha.word s₂
  obtain ⟨bits₃,w₃,e₃⟩:=travel Data.table good alpha.word s₂
  obtain ⟨st,land⟩:=Bool.and_eq_true_iff.mp checked
  have init : agrees (carrier s₂) alpha.start := by
    rw [firstSig]; unfold agrees LevelOne.maskH; rw [Nat.and_assoc,Nat.and_self]
  have reached : Masked s₃ alpha.target := by
    unfold Masked; rw [bits₃]
    exact (walk_agrees alpha.word st init).trans (eq_of_beq land)
  obtain ⟨s₄,match₄,z₄,r₄,w₄,e₄,reach₄⟩:=repair good s₃
  have mask₄ : Masked s₄ alpha.target := match₄.trans reached
  obtain ⟨rows,len,complete,packet⟩:=perProfile _ target
  have small₄ : errors full3 s₄≤92 := ((w₄.trans w₃).trans (w₂.trans ht.2.1)).le.trans low
  have hit:=completion_in_codes s₄ alpha.target mask₄ z₄ r₄ small₄ rows len complete
  obtain ⟨beta,sourceβ,out,ok⟩:=packet _ hit
  obtain ⟨bits₅,_,e₅⟩:=travel Data.table good beta.word s₄
  have dest : walk Data.table beta.word beta.start=beta.target := eq_of_beq ok
  have reach₁ : Reach Data.table s s₁ := ⟨w,rfl⟩
  have reach₃ : Reach Data.table s₂ s₃ := ⟨alpha.word,rfl⟩
  have reach₅ : Reach Data.table s₄ (action Data.table beta.word s₄) := ⟨beta.word,rfl⟩
  refine ⟨action Data.table beta.word s₄,?_,?_,reach₁.trans (reach₂.trans (reach₃.trans (reach₄.trans reach₅)))⟩
  · rw [bits₅,←sourceβ,dest]; exact out
  · exact e₅.trans (e₄.trans (e₃.trans (e₂.trans ht.2.2)))

end Quadric.Five.Moves

