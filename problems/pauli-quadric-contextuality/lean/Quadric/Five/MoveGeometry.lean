import Quadric.Five.Paths
import Quadric.Five.SortWitness
import Quadric.Five.Resources.MoveLines

namespace Quadric.Five.Moves.Data
open Small Tagged

noncomputable def checkGeometry (m : Move) := fastLineOK m insideLines && fastLineOK m outerLines
theorem geometry_checked (m : Move) (hr : routeOK m=true) (h : checkGeometry m=true) : Good m := by
  obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp h
  refine ⟨hr,?_,?_⟩
  · rw [inside_points]; exact fastLine_perm a
  · rw [outer_points]; exact fastLine_perm b

end Quadric.Five.Moves.Data
