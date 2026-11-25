import MABKCore

#print MABK.conjecture1
#print MABK.uniformValues
#print MABK.HilbertBehavior.Realizes
#print MABK.publishedMstar
#print MABK.mabk
#print MABK.eq24
#print MABK.publishedAngle
#print MABK.angleIndex
#print MABK.radius
#check MABK.zero_correlator_bound
#check MABK.tensor_attainment
#print axioms MABK.conjecture1
#print axioms MABK.uniform_upper
#print axioms MABK.zero_correlator_bound
#print axioms MABK.tensor_realization
#print axioms MABK.tensor_attainment
#print axioms MABK.all_even_torus

run_cmd do
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  let actual ← Lean.collectAxioms ``MABK.conjecture1
  unless actual.all expected.contains && expected.all actual.contains do
    throwError "Unexpected axiom set for MABK.conjecture1: {actual}"
