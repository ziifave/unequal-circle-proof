import CirclePacking.FifteenStageZeroCanonicalGeometry

/-! Targeted axiom audit for the geometric normalization bridge. Run with
`lake env lean CirclePacking/FifteenStageZeroTransportAudit.lean`. The finite
replay audit remains in `FifteenTrustAudit.lean`. -/

#print axioms CirclePacking.fifteenStage0Profile_canonical_dihedral
#print axioms CirclePacking.fifteenStage0DihedralAngles_ordered
#print axioms CirclePacking.fifteenStage0DihedralAngles_distance_sq
#print axioms CirclePacking.fifteenStage0PolarProfile_excludes_cycle_witness
#print axioms CirclePacking.fifteen_unit_packing_wall_push_stage0_canonical_geometry
