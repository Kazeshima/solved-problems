import Quadric.Five.CensusCounts
import Quadric.Five.Resources.LevelOne
namespace Quadric.Five.Census.LevelOne
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
private theorem unique0 : chunk0.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique1 : chunk1.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique2 : chunk2.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique3 : chunk3.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique4 : chunk4.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique5 : chunk5.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique6 : chunk6.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique7 : chunk7.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique8 : chunk8.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique9 : chunk9.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique10 : chunk10.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique11 : chunk11.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique12 : chunk12.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique13 : chunk13.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique14 : chunk14.all (uniqueBelow 65536)=true := by decide +kernel
private theorem unique15 : chunk15.all (uniqueBelow 65536)=true := by decide +kernel
theorem all_bounded_unique : survivors.all (uniqueBelow 65536)=true := by
  unfold survivors; simp only [List.all_append,unique0,unique1,unique2,unique3,unique4,unique5,unique6,unique7,unique8,unique9,unique10,unique11,unique12,unique13,unique14,unique15,Bool.and_self]
theorem distinct_survivors : (survivors.map (fun r=>r.toFinset.card)).sum=18752 :=
  (count_distinct all_bounded_unique).trans lengths.2
end Quadric.Five.Census.LevelOne
