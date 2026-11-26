import Quadric.Five.BlockGeometry
import Quadric.Five.Resources.System10

namespace Quadric.Five.Census.Block.Case10
open Small
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
set_option Elab.async false

private theorem sameForms : ((splitForms system).map normalized).Perm
    ((crossing.map (lineForm freePoints restriction)).map normalized) := by decide +kernel

theorem outside_cost (s : ℕ→Bool) :
    fullCost system (field s 20 11) (field s 0 10) (field s 10 10)=errors crossing (extendBits freePoints restriction s) :=
  actual_cost system freePoints restriction s (by unfold widths; decide +kernel) sameForms

private theorem fixedBits : fixedSection freePoints=true := by decide +kernel
private theorem threshold_sum : errors sections restriction.testBit+system.cutoff=92 := by decide +kernel

theorem threshold_iff (s : ℕ→Bool) : errors full3 (extendBits freePoints restriction s)≤92 ↔
    fullCost system (field s 20 11) (field s 0 10) (field s 10 10)≤system.cutoff := by
  rw [partition,section_fixed _ _ _ fixedBits,outside_cost]
  have := threshold_sum; omega

end Quadric.Five.Census.Block.Case10
