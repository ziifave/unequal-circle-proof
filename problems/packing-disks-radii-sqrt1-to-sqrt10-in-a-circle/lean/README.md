# Lean formalization layer

This directory starts a proof-assistant layer for the unequal-circle packing
problem.  The first layer is deliberately algebraic: it defines points,
circles, containment, pairwise separation, packings, and monotonicity under
enlarging the container.

The Python/MPFI programs remain the numerical-search and certificate
generation layer.  They are not trusted by Lean merely because they produce a
file.  The intended interface is a small Lean checker for each certificate:

1. exact rational or algebraic interval endpoints;
2. finite inequalities checked by Lean arithmetic;
3. a finite cover of the continuous search region;
4. a final theorem assembling the checked certificates.

The first certificate interface is now in `CirclePacking/Certificate.lean`.
It proves that finitely many linear inequalities are inconsistent when a
nonnegative weighted combination has zero left-hand side and strictly
positive right-hand side.  `CirclePacking/Angle.lean` connects certified
cosine inequalities to `arccos` lower bounds, and
`CirclePacking/Angular.lean` connects those bounds to the finite angular
Farkas contradiction used by the numerical search.

`CirclePacking/CosineTaylor.lean` contains kernel-checked Taylor remainder
estimates for `Real.cos`, including an order-96 bound used for angles near
`pi`.  The rational Taylor inequalities are discharged by `native_decide` and
then interpreted in `Real`; no floating-point trigonometric call is used by
the Lean replay.

The finite combinatorial replay for the seven-circle `rho=7.9` certificate is
now in `CirclePacking/SevenNine.lean`.  Its 46,080 cell records are stored as
a compact decimal mask file in `certificates/` and imported with Lean's
`include_str`; the source does not contain a giant `Array Rat`.  The replay
parses the masks, reconstructs the 360 orders and 128 radial states per order,
and checks all column bounds and strict rational Farkas sums in 180 chunks via
`native_decide`.  This keeps elaboration and memory use manageable while
retaining a small, inspectable Lean theorem for the finite layer.

`CirclePacking/SevenNineAngleProofs.lean` connects the 84 exported rational
angle records to analytic inequalities: 76 nonzero records receive explicit
theorems, while zero records are handled by the nonnegative-angle branch.
Each theorem proves the shared-radius rectangle bound using the kernel-checked
four-corner lemma, proves the square-root distance enclosure, proves the
cosine comparison with the order-96 Taylor remainder, and concludes with the
`arccos` monotonicity lemma.  The cosine upper data are rounded upward; radial
and distance data are rounded outward.

The analytic connection and the compact 46,080-cell finite Farkas replay are
both imported by `CirclePacking.lean` and pass `lake build CirclePacking`.
`CirclePacking.SevenNineCoverage` now also proves, for an arbitrary real
`Packing`, the analytic radial bounds and the finite binary choice that places
each radial coordinate in one exported subinterval.  Its theorem
`sevenNine_packing_is_covered` combines this with explicit finite endpoint
lemmas.  The endpoint comparisons use only exact rational arithmetic and the
already replayed downward square-root bounds; they are not hidden behind an
axiom.

`tools/export_lean_angular_certificate.py` now performs the first data
conversion for the existing six-circle certificate.  It emits downward-rounded
rational angle bounds, upward-rounded contact-cosine bounds, and upward-rounded
rational weights in
`artifacts/*-lean.json`.  The generated data is intentionally not yet a Lean
theorem: cosine-bound replay is the remaining soundness obligation.

## Trust boundary

At this stage no global optimality theorem is claimed.  The Lean files certify
the definitions, the finite Farkas implication, the `arccos` monotonicity
step, the angular contradiction, the cosine Taylor remainder, the 84 concrete
angle-enclosure connections, the geometric implication from arbitrary
packings to analytic radial bounds, and the finite MPFI endpoint comparison
for the exported radial partition.  The remaining trust boundary is the
external generation of the exported rational data itself.

## Global proof entry point

`CirclePacking/GlobalOptimality.lean` is the focused Lean entry point for the
global proof.  The optimum is defined by the unique solution of the exact
angle equations; identifying it with the separate high-degree polynomial root
`R0` is not needed.  `CirclePacking/GlobalAnchorRadius.lean` proves directly
from the packing axioms that if disk 9 has radius 3, disk 10 has radius
`sqrt 10`, and disk 10's center radius is at most `2253/2000`, then the
container radius is strictly greater than `15947/2000`.

`CirclePacking/CertificateTree.lean` formalizes coverage for a finite tree of
rational box splits.  Each child box is indexed by the parent's exact cut, and
Lean proves that every point in the root box belongs to a leaf box.  This is
the structural coverage layer only; contractor soundness, the concrete
radial-tree data, and its terminal exclusions still need to be connected.

`CirclePacking/RadialPropagation.lean` proves that a pairwise radial
contraction, and any finite sequence of such contractions, preserves every
packing represented by the input box.

`CirclePacking/GlobalRadialBox.lean` now checks the ten downward-rounded
square-root lower bounds from the global certificate as exact rational
inequalities.  It derives the initial rational radial box from container
containment and pairwise separation, then composes the all-pairs contractor to
prove that every ten-circle packing below the certificate's radius upper
bound remains in the propagated root box.  It also combines this result with
the generic split-tree coverage theorem: any rational split tree rooted at
that box has a leaf containing the packing's radial vector.  The actual
exported radial tree and main-order leaf exclusions are still outside Lean.

`CirclePacking/PropagatedSplitTree.lean` models the search's per-node order:
contract the current box, split the contracted box, and contract again at each
child.  Its generic coverage theorem is connected to the ten-circle geometry
by `tenCircle_propagatedGlobalTree_covers`.  Thus arbitrary packings are now
proved to reach a leaf of any correctly indexed tree with that node structure;
the exported node data and each leaf's exclusion certificate remain to be
replayed.

`CirclePacking/NineCircleCertificate.lean` now replays the concrete
two-order, 308-node nine-circle certificate. The generated data contains 155
cycle leaves; Lean checks every split point, each exact integer cross-product
for a Taylor/corner inequality, and every strictly negative cycle sum. The
input JSON is pinned by SHA-256 in
`tools/export_nine_circle_certificate_lean.py`. Regenerate it from the
repository root and build it with:

```sh
uv run python tools/export_nine_circle_certificate_lean.py
cd lean
lake build CirclePacking.NineCircleCertificate
```

## 15-disk certificate: first Lean replay layer

`CirclePacking/FifteenCertificate.lean` reads the exact JSON subdivision tree
and `research/fifteen_equal_completion/candidate_bundle/full_residuals.txt`
directly with `include_str`. Its `fifteenExactCertificate_replays` theorem
checks that the 1,266 supplied roots match the listed residual assignments,
then replays all 58,860 tree nodes using rational endpoints. Every split must
select an inner coordinate, use its exact rational midpoint, and pass the
corresponding left and right boxes to its children. The file also proves
one-coordinate lemmas showing that an in-range split covers its parent
interval and that both child intervals stay inside the parent.

At terminal leaves Lean checks pair-sum contradictions and replays each
negative cycle's directed edge connectivity, edge labels, recorded integer
ticks, and strictly negative integer total. It checks 30,032 cycle leaves,
31 local leaves, and all nine branches for the three 6+9 residual assignments.
The integer ticks are still treated as supplied data here: connecting each
tick to its geometric angle lower bound is the next formalization layer.
Likewise, matching the roots to `full_residuals.txt` does not yet certify the
upstream 760-orbit enumeration. This is a replay of the rational subdivision
certificate, not yet a Lean proof of the 15-disk optimum.

Build this layer with:

```sh
cd lean
lake build CirclePacking.FifteenCertificate
```

For a WSL checkout under `/mnt/c`, the focused build can be much faster by
running `bash tools/build_fifteen_certificate_fast.sh` from the repository
root. It copies this module and its two input files to `/tmp`, then builds the
same target there. This works because the current module imports only core
Lean. On this machine, the regular target took 123 seconds, while the
Linux-filesystem copy took 5.7 seconds initially and 1.9 seconds with its cache
warm. This helper only checks the 15-disk replay module; it is not a
replacement for building the full Mathlib-backed project, and should be
updated if this module gains imports.

As with the existing finite replay, this theorem currently uses `native_decide`;
`#print axioms` reports its native-evaluation axiom in addition to Lean's
standard logical axioms. The final trust/dependency audit remains outstanding.

This finite arithmetic replay uses
`native_decide`, whose evaluator is an additional trust dependency. The
theorems `nineCircleProofP_spec` and `nineCircleProofQ_spec` convert each
successful Boolean replay into the proposition `nineCertificateSpec`,
exposing the exact scale, radius bounds, recursive split checks, edge checks,
and negative cycle weights. `NineCircleCertificateSoundness.lean` now
continues the edge path: it converts the stored integer Taylor/corner checks
to a real cosine inequality, normalizes the four radial corners by the
certificate scale, derives a lower bound on the actual touch angle, and
turns that into the directed angular inequality for an edge of a separated
packing. The natural-number cycle metadata is mapped to `Fin 9`; its tail
specification yields a closed angular walk. The negative integer tick sum is
also proved to equal the corresponding negative real edge-weight sum. Together
these give `nineLeafSpec_negative_cycle_excluded`: any checked leaf is
geometrically impossible once its per-edge angular bounds are supplied.
`nineLeafSpec_excludes_polar_configuration` supplies those bounds from a
single normalized polar configuration, assuming its radial coordinates lie
in the leaf box, its disk radii dominate the certified lower radii, and its
disks are pairwise separated in the certified cyclic order.

`nineReplayTree_excludes_scaled_configuration` now composes this leaf result
through an arbitrary replayed split tree. It follows the configuration into
one child at every cut. The theorem derives contractor preservation from
pairwise separation, radius lower bounds, and the triangle inequality: each
contractor lower bound is at most the corresponding scaled center radius, and
the finite maximum used by the checker preserves that inequality. Box endpoint
ordering follows from membership itself. `NineCirclePackingSoundness.lean`
also proves that the certificate labels yield an injective map into the ten
standard radii and packages this as concrete exclusion theorems for both
checked certificates. The remaining work is to establish the required
cyclic-order cases and connect their coverage to the global proof.

`NineCirclePackingSoundness.lean` supplies `nineCertificate_excludes_polar_order`,
which accepts an explicit polar representation in any normalized coordinate
frame. This separates the geometric replay from the choice of angle origin and
supports the cyclic-order rotation step. `nineCertificate_excludes_cyclic_packing_order`
now rotates the whole packing so the first certificate slot becomes angle zero,
using proved rotation invariance of containment and separation. The existing
`nineCertificate_excludes_packing_order` theorem is the `Complex.arg`
specialization, with angles in `[0, 2π]`. Both take a `Packing 10 R` whose
anchor circle is centered at the container origin and whose other nine
circles are supplied in one certificate's cyclic order. They derive the initial
radial box from containment, obtain outer-circle separation from the packing
axiom, and invoke the checked split-tree exclusion. Matching each slot to its
certified disk radius is now derived for the two concrete certificates under
the standard radius assignment `radius(k)^2 = k + 1`. The caller still has to
establish that the labels occur in the certificate's cyclic order; the
absolute choice of angle origin no longer matters. Concrete P and Q
corollaries now combine the radius map, certificate label order, and cyclic
normalization. Other cyclic orders still require coverage.

`CirclePacking/NineCircleGeometry.lean` formalizes the general geometric
bridge: four corner bounds over a radial box imply a touch-angle lower bound;
non-overlap turns this into a directed angle-gap bound; and summing those
bounds around any closed walk contradicts a strictly negative total. The
alternate P/Q orders are connected to packing exclusions by the finite
projection module described below. The main-order angle-barrier cases and the
concrete radial tree remain to be replayed.

`CirclePacking/AlternateOrderProjection.lean` now replays the finite order
projection for the two residual sector-mask types. It bit-decodes the masks
`(5,16,40,2)` and `(4,16,41,2)`, exhausts the sector-local permutations, and
proves that deleting disk 1 leaves one of the two checked P/Q orders. Its
`alternateCaseA_excluded_of_sector_permutations` and
`alternateCaseB_excluded_of_sector_permutations` theorems compose this finite
fact with the existing nine-circle packing exclusions. They assume that each
sector list is a permutation of its decoded mask labels and that the full
interleaved order is monotone in lifted polar angle. Deriving those premises
from the global radial-tree terminal cases, replaying the main-order
exclusions, and the final global assembly remain outstanding.

`CirclePacking/LargeFourSemicircle.lean` now proves the four-large-circle
half-plane obstruction directly from a packing. It replays the rational
square-root lower bounds, derives each center's radial interval from
containment and separation, and checks the six angle bounds by exact rational
corner inequalities plus the cosine Taylor remainder theorem. It then orders
the four polar angles and derives that a common closed half-plane would put
them in an interval of width π, contradicting the checked path sums for all
24 orders. The exported theorem is
`largeFour_packing_not_in_closed_halfplane`; it assumes `R ≤ U` and that the
four designated radii are exactly `sqrt 7`, `sqrt 8`, `sqrt 9`, and `sqrt 10`.
The remaining global work is to show that every candidate packing in the
certificate's terminal cases satisfies this obstruction's hypotheses and to
replay/assemble the full radial tree and the main-order angle-barrier cases.

The two alternate nine-circle certificates, their geometric soundness, the
finite P/Q order projection, and the rational path-angle obstruction are
replayed by Lean. The radial tree, the
main-order angle-barrier certificates, and the derivation of the required
sector-order hypotheses from the global terminal cases are still checked only
by the exact Python composition verifier. This remains a partial Lean
formalization, not yet a Lean proof of global optimality. Build the focused
global entry point with `lake build CirclePacking.GlobalOptimality`.

Build with:

```text
lake update
lake build
```

On WSL, the repository may live under `/mnt/c`, where Lake's many small file
accesses are slow. To build the full `CirclePacking` library on the Linux
filesystem while keeping the working tree on Windows, run this from the
repository root:

```text
./tools/build_lean_linux_mirror.sh
```

The script syncs the Lean sources and embedded certificate inputs into
`~/unequal-circle-proof-linux`, seeds its Lake cache once from the existing
4.6 GB cache, and runs `lake build CirclePacking` there. Later invocations
incrementally sync source changes and reuse the Linux-side cache. To build a
different target, pass it as an argument, for example
`./tools/build_lean_linux_mirror.sh CirclePacking.FifteenCertificate`.
Set `UNEQUAL_LAKE_MIRROR` to choose a different Linux-native destination. The
focused `build_fifteen_certificate_fast.sh` remains a separate, smaller check;
it does not build the full Mathlib-backed library.
