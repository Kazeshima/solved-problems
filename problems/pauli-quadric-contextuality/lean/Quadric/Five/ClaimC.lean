import Quadric.Five.Resources.CensusCount
import Quadric.Five.Exact
import Quadric.Five.Reduction
import Quadric.Five.FortyTwo
import Quadric.Five.LevelOneGeometry
import Quadric.Five.Resources.HyperplaneData
import Quadric.Five.ScreenSound

namespace Quadric.Five

/-- Bounds using the attained five-qubit witness and the all-rank moment inequality. -/
theorem five_qubit_bounds : 6426≤degree 5 ∧ degree 5≤6975 := ⟨spectral_lower,witness_upper⟩

end Quadric.Five
