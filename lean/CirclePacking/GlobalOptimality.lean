import CirclePacking.Basic
import CirclePacking.Angle
import CirclePacking.Angular
import CirclePacking.AngularCellCertificate
import CirclePacking.FiniteOptimality
import CirclePacking.Optimality
import CirclePacking.ParametricOptimality
import CirclePacking.GlobalAnchorRadius
import CirclePacking.CertificateTree
import CirclePacking.RadialPropagation
import CirclePacking.PropagatedSplitTree
import CirclePacking.GlobalRadialBox
import CirclePacking.NineCircleCertificate
import CirclePacking.NineCircleGeometry
import CirclePacking.NineCirclePackingSoundness

/-!
# Lean entry point for the global optimality proof

This module follows the angle-defined critical radius used by the global
proof.  It does not import the optional high-degree algebraic eliminants for
the separate root `R0`.

The reusable proof layers are available here: Euclidean packing predicates,
the angular Farkas contradiction, finite-cover assembly, parametric optimality
assembly, and the two-anchor radius-floor lemma.  The concrete radial tree and
main-order angle-barrier cases remain in the Python verifier.  The alternate
nine-circle payload has a Lean arithmetic replay.  `NineCircleGeometry.lean`
now proves the generic bridge from four radial-box corner inequalities and
non-overlap to directed angular edge bounds, and proves that a negative closed
cycle of those bounds is impossible.  The concrete finite Boolean checker has
been reflected to `nineCertificateSpec`; its edge checks now imply angular
bounds, and a generic theorem turns each negative cycle leaf into a geometric
exclusion once those bounds hold for the packing.  Instantiating the box and
packing hypotheses across the concrete tree remains in progress.

`RationalSplitTree.covered` proves structural coverage for ordinary rational
splits.  `PropagatedSplitTree.covered` also models contractor-before-split at
every node; the concrete certificate tree has not yet been instantiated in
either interface.

`RationalBox.packing_pair_propagation_sound` proves the geometric contractor
step used by the radial search, and `packing_allPairPropagation_sound` proves
that applying it to every distinct ordered pair preserves every actual
packing.

`CirclePacking/GlobalRadialBox.lean` now replays the certificate's ten exact
downward square-root bounds, derives the global initial radial box from
containment and separation, and proves that the full distinct-pair propagation
preserves every ten-circle packing below the certificate's rational radius
upper bound.  Any rational split tree rooted at that propagated box is then
proved to cover every such packing.  The concrete exported tree and main-order
terminal exclusions still need to be replayed.

`CirclePacking/PropagatedSplitTree.lean` additionally models the actual search
order: every node contracts its box, then splits the contracted box, and its
children contract again.  Its generic coverage theorem is connected to the
ten-circle geometry by `tenCircle_propagatedGlobalTree_covers`.

`CirclePacking/NineCircleCertificate.lean` replays the concrete two-order
nine-circle certificate: 308 tree nodes, 155 cycle leaves, all exact Taylor
corner comparisons, and all strict cycle sums.  The source JSON is pinned by
SHA-256 and converted to a common-scale integer representation.  This replay
uses Lean's `native_decide`, so its theorem has that evaluator's trust
dependency. `NineCircleCertificateSoundness.lean` now connects these checks
to edge angle bounds and proves that any checked cycle leaf is impossible for
a normalized polar configuration inside its radial box. The tree exclusion
theorem now composes the leaf contradiction through the recursive split tree,
deriving contractor preservation from pairwise separation, radius lower
bounds, and the triangle inequality; endpoint ordering follows from box
membership. The Packing connection is now formalized for a `Packing 10 R`
whose anchor is at the container origin and whose other nine circles follow
the certificate's specified cyclic order. For both checked certificates,
`NineCirclePackingSoundness.lean` proves an injective map from certificate
slots to the standard ten radii and gives concrete packing-exclusion
corollaries. Its new `nineCertificate_excludes_polar_order` interface accepts
explicit normalized polar coordinates independently of `Complex.arg`, which
is the interface needed to normalize a cyclic order by rotating its angle
origin. Deriving the needed cyclic orders from arbitrary packings,
covering the remaining order cases, replaying the main-order exclusions, and
the final global assembly remain outstanding.
-/

namespace CirclePacking

structure GlobalOptimalityCertificate
    (X : Type) (n : ℕ) (Feasible : ℝ → X → Prop) (L Rcrit : ℝ) where
  witness : ∃ x, Feasible Rcrit x
  belowFloorExcluded : ∀ R, R < L → ¬ ∃ x, Feasible R x
  finiteExclusion : ParametricFiniteCertificate X n Feasible L Rcrit

theorem GlobalOptimalityCertificate.isLeast
    {X : Type} {n : ℕ} {Feasible : ℝ → X → Prop} {L Rcrit : ℝ}
    (cert : GlobalOptimalityCertificate X n Feasible L Rcrit) :
    IsLeast {R : ℝ | ∃ x, Feasible R x} Rcrit := by
  apply isLeast_of_parametric_finite_certificate
  · exact cert.witness
  · exact cert.belowFloorExcluded
  · exact cert.finiteExclusion

end CirclePacking
