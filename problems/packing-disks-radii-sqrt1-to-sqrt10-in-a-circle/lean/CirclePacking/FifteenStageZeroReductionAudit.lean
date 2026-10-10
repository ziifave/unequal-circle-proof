import CirclePacking.FifteenStageZeroFiniteReduction

/-! Targeted audit of enumeration coverage and the packing-level Stage 0
reduction. The proofs reuse the existing finite replay, without adding a
new native-evaluation theorem. -/

#print axioms CirclePacking.fifteenStage0Assignment_covered
#print axioms CirclePacking.fifteenStage0SurvivorPatterns_length
#print axioms CirclePacking.fifteenStage0LabelProfile_count
#print axioms CirclePacking.fifteenStage0LabelProfile_covered
#print axioms CirclePacking.fifteen_unit_packing_wall_push_stage0_dihedral_label_counts
#print axioms CirclePacking.fifteenStage0PolarProfile_survives
#print axioms CirclePacking.fifteen_unit_packing_wall_push_stage0_survivor_geometry
