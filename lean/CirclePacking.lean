import CirclePacking.Basic
import CirclePacking.Certificate
import CirclePacking.Angle
import CirclePacking.Angular
import CirclePacking.CertificateFormat
import CirclePacking.CosineCertificate
import CirclePacking.CosineTaylor
import CirclePacking.CornerBound
import CirclePacking.SevenNineAngleData
import CirclePacking.SevenNine
import CirclePacking.SevenNineAngleProofs
import CirclePacking.SevenNineCoverage
import CirclePacking.RootIsolation
import CirclePacking.HennebergCore
import CirclePacking.G112
import CirclePacking.FiniteOptimality
import CirclePacking.SevenNineFiniteOptimality
import CirclePacking.AngularCellCertificate
import CirclePacking.GeometricAngle
import CirclePacking.CyclicGap
import CirclePacking.PolarAngle

/-!
# Formal algebraic core for unequal-circle packing

The finite replay is paired with explicit angle-enclosure proofs in
`CirclePacking.SevenNineAngleProofs`.  The geometric implication from an
arbitrary `Packing` to the analytic radial bounds, and the finite-choice
coverage theorem for the radial boxes, are in
`CirclePacking.SevenNineCoverage`.  The remaining numerical boundary is the
external generation of the MPFI-exported rational data; its endpoint
comparisons are replayed by the coverage file.
-/
