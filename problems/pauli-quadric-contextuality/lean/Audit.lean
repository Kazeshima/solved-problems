import Quadric

#check Quadric.contextuality_bounds
#check Quadric.contextuality_limit
#check Quadric.Four.degree_four
#check Quadric.Four.optimal_projector
#check Quadric.Four.flat_iff_optimal
#check Quadric.Dual.points_match
#check Quadric.Dual.pencils_match
#check Quadric.Dual.plucker_points
#check Quadric.Dual.plucker_pencils
#check Quadric.Five.spectral_lower

#print axioms Quadric.hermitian_iff
#print axioms Quadric.pauli_injective
#print axioms Quadric.context_iff_commute
#print axioms Quadric.context_product
#print axioms Quadric.point_count
#print axioms Quadric.line_count
#print axioms Quadric.trace_one
#print axioms Quadric.trace_two
#print axioms Quadric.trace_three
#print axioms Quadric.trace_power
#print axioms Quadric.cubic_bound
#print axioms Quadric.upper
#print axioms Quadric.contextuality_bounds
#print axioms Quadric.contextuality_limit
#print axioms Quadric.Four.degree_four
#print axioms Quadric.Four.optimal_spectrum
#print axioms Quadric.Four.optimal_projector
#print axioms Quadric.Four.flat_iff_optimal
#print axioms Quadric.gauge_extends
#print axioms Quadric.Four.chart_matrix_update
#print axioms Quadric.Four.chart_pencil_violated
#print axioms Quadric.Dual.points_match
#print axioms Quadric.Dual.pencils_match
#print axioms Quadric.Dual.plucker_points
#print axioms Quadric.Dual.plucker_pencils
#print axioms Quadric.Five.spectral_lower

#check Quadric.Clifford.normal
#check Quadric.Four.optimal_iff_canonical_orbit
#check Quadric.Four.every_optimal_assignment
#check Quadric.Four.every_optimum_in_orbit
#check Quadric.Four.optimal_assignments_count
#check Quadric.Four.optimal_configurations_count
#check Quadric.Four.DWIso.incident
#check Quadric.Four.every_optimum_DW
#check Quadric.Four.classification

#print axioms Quadric.Four.profiles
#print axioms Quadric.Four.heavy_wave
#print axioms Quadric.Four.heavy_at_count
#print axioms Quadric.Four.incidence_count
#print axioms Quadric.Four.gauge_fiber_card
#print axioms Quadric.Four.optimal_iff_canonical_orbit
#print axioms Quadric.Four.every_optimal_assignment
#print axioms Quadric.Four.every_optimum_in_orbit
#print axioms Quadric.Four.optimal_assignments_count
#print axioms Quadric.Four.optimal_configurations_count
#print axioms Quadric.Four.every_optimum_DW
#print axioms Quadric.Four.classification

#check Quadric.Five.five_qubit_bounds
#print axioms Quadric.Five.five_qubit_bounds
#check Quadric.Five.witness_count
#print axioms Quadric.Five.witness_count
#check Quadric.Five.degree_ne_6975975
#print axioms Quadric.Five.degree_ne_6975975
#check Quadric.Five.canonical_centres5
#print axioms Quadric.Five.canonical_centres5
#check Quadric.Five.five_from_full_four
#print axioms Quadric.Five.five_from_full_four
#check Quadric.Five.one_elliptic_suffices
#print axioms Quadric.Five.one_elliptic_suffices
#check Quadric.Five.elliptic_reduction
#print axioms Quadric.Five.elliptic_reduction
#check Quadric.Five.exact_of_catalogues
#print axioms Quadric.Five.exact_of_catalogues
#check Quadric.Five.Certificates.certificate_bound
#print axioms Quadric.Five.Certificates.certificate_bound
#check Quadric.Five.Certificates.gram_positive
#print axioms Quadric.Five.Certificates.gram_positive
#check Quadric.Five.Census.LevelOne.coverage
#print axioms Quadric.Five.Census.LevelOne.coverage
#check Quadric.Five.Census.LevelOne.lengths
#print axioms Quadric.Five.Census.LevelOne.lengths
#check Quadric.Five.Census.LevelOne.section_census
#print axioms Quadric.Five.Census.LevelOne.section_census
#check Quadric.Five.Small.HyperplaneData.low_section
#print axioms Quadric.Five.Small.HyperplaneData.low_section
#check Quadric.Five.Certificates.all_42_certificates
#print axioms Quadric.Five.Certificates.all_42_certificates
#print axioms Quadric.Five.Certificates.distinct_42

#check Quadric.Five.Census.LevelOne.distinct_survivors
#print axioms Quadric.Five.Census.LevelOne.distinct_survivors

#check Quadric.Five.Census.distinct_completion_count
#print axioms Quadric.Five.Census.distinct_completion_count

#check Quadric.Five.hyperplane_profile_count
#print axioms Quadric.Five.hyperplane_profile_count

#check Quadric.Five.census_classification
#print axioms Quadric.Five.census_classification

#check Quadric.Five.all_low_signatures_in_orbits
#print axioms Quadric.Five.all_low_signatures_in_orbits

#check Quadric.Five.every_low_restriction
#print axioms Quadric.Five.every_low_restriction

#check Quadric.Five.degree_five
#print axioms Quadric.Five.degree_five

example : Quadric.degree 5 = 6975 := Quadric.Five.degree_five
