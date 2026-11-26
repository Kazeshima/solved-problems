import Quadric.Five.MoveGeometry

namespace Quadric.Five.Moves.Data
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option Elab.async false
theorem geometry0 : checkGeometry m0=true := by decide +kernel
theorem geometry1 : checkGeometry m1=true := by decide +kernel
theorem geometry2 : checkGeometry m2=true := by decide +kernel
theorem geometry3 : checkGeometry m3=true := by decide +kernel
theorem geometry4 : checkGeometry m4=true := by decide +kernel
theorem geometry5 : checkGeometry m5=true := by decide +kernel
end Quadric.Five.Moves.Data
