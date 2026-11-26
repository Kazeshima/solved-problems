import Quadric.Five.FramePhysics

namespace Quadric.Five.Moves.Data
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option Elab.async false
private theorem check64 : gaugeCheck 64=true := by decide +kernel
private theorem check65 : gaugeCheck 65=true := by decide +kernel
private theorem check66 : gaugeCheck 66=true := by decide +kernel
private theorem check67 : gaugeCheck 67=true := by decide +kernel
private theorem check68 : gaugeCheck 68=true := by decide +kernel
private theorem check69 : gaugeCheck 69=true := by decide +kernel
private theorem check70 : gaugeCheck 70=true := by decide +kernel
private theorem check71 : gaugeCheck 71=true := by decide +kernel
theorem all_gauges : (List.range' 64 8).all gaugeCheck=true := by
  rw [show List.range' 64 8=[64,65,66,67,68,69,70,71] by decide]
  simp only [List.all_cons,List.all_nil,check64,check65,check66,check67,check68,check69,check70,check71,Bool.and_self]
end Quadric.Five.Moves.Data
