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

The upstream coarse stage is independently replayed in
`CirclePacking/FifteenStageZero.lean`. Lean enumerates all 15-bit words with
5--8 inner positions, takes the minimum over rotations and reflections, and
checks that the resulting classes are exactly 111, 185, 232, and 232 (760 in
total). For each of the 382 classes rejected by the coarse graph, it regenerates
the complete set of radial-type assignments allowed by the rank constraints
and verifies an integer negative-cycle witness for every assignment. For the
other 378 classes, it checks a surviving assignment and an integer potential
that certifies the corresponding coarse difference-constraint graph has no
negative cycle. The same replay checks all positive entries in the coarse
4-by-4 angle table against the rational Taylor/corner checker used by the
subdivision layer.
`CirclePacking/FifteenStageZeroGeometry.lean` turns each positive coarse-table
entry into a touch-angle lower bound for every radius pair in the corresponding
radial rectangles, using the general corner and Taylor soundness theorems.

The compact inputs
`problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage0_cycles.txt` and
`stage0_orbits.txt` are generated from the tracked compressed source
certificate by `export_lean_stage0_certificate.py`. The exporter is not part
of Lean's trust boundary: Lean validates the orbit list, every assignment,
every referenced edge, and all signed integer sums itself. Build the core-only
replay quickly on WSL with:

```sh
bash tools/build_fifteen_stage0_fast.sh
```

This closes the 760-orbit replay in Lean. The 378-to-23 and 23-to-4 radial-type
pruning steps are now replayed by `CirclePacking.FifteenStages34` and
`CirclePacking.FifteenStage4`; their Boolean certificate checks use
`native_decide`, so their native-evaluation dependency remains part of the
trust boundary.

`CirclePacking/FifteenCertificate.lean` reads the exact JSON subdivision tree
and `problems/packing-15-equal-disks-in-a-circle/candidate_bundle/full_residuals.txt`
directly with `include_str`. Its `fifteenExactCertificate_replays` theorem
checks that the 1,266 supplied roots match the listed residual assignments,
then replays all 58,860 tree nodes using rational endpoints. Every split must
select an inner coordinate, use its exact rational midpoint, and pass the
corresponding left and right boxes to its children. The file also proves
one-coordinate lemmas showing that an in-range split covers its parent
interval and that both child intervals stay inside the parent.

At terminal leaves Lean checks pair-sum contradictions and replays each
negative cycle's directed edge connectivity, edge labels, integer ticks, and
strictly negative integer total. The checker also recomputes each regular
edge's corner cosine cap and verifies that its recorded tick is safe under an
exact rational degree-18 Taylor lower bound. It checks 30,032 cycle leaves,
31 local leaves, and all nine branches for the three 6+9 residual
assignments. The upstream 760-orbit enumeration is independently replayed by
`CirclePacking/FifteenStageZero.lean`. The finer radial-type filters are
replayed in `CirclePacking/FifteenStages34.lean` and
`CirclePacking/FifteenStage4.lean`; deriving every pruning predicate from the
geometric packing hypotheses remains a separate soundness task.

`CirclePacking/FifteenTickSoundness.lean` proves that the degree-18 Taylor
polynomial minus its `x^19 / 18!` remainder is below `cos x` for every
certificate angle `x = q / 2800`, with `q ≤ 8790`. For a regular cosine cap
in `(-1, 1)`, `fifteenRegularTick_gives_angle_lower_bound` then proves that an
accepted tick is a lower bound on any contact angle whose cosine is below
that cap. This remainder is more conservative than the Python checker's
degree-18 `x^19 / 19!` bound; every stored cycle tick still passes the
stronger Lean remainder check.

The theorem `fifteenRegularTick_lower_bounds_center_angle` connects a regular
checked tick to the geometry of a separated pair of centers. Given positive
radial intervals, radii inside those intervals, and squared center distance at
least 4, it proves that the centers' angle is at least the tick. Its proof
establishes that the cosine-rule cap over the whole rectangle is bounded by the
maximum of its four rational corners, then applies the disk separation
inequality. The lower-bound part is factored as
`fifteenRegularTick_lower_bounds_touch_angle`.

The signed polar-order bridge is now formalized for regular edges.
`fifteen_polar_touch_angle_ordered_gap` turns a contact-angle lower bound into
bounds on both directed gaps between two sorted polar angles. Then
`fifteen_polar_edge_respects_angular_bound` proves the signed upper bound used
by the negative-cycle argument, for either edge direction. Finally,
`fifteenRegularTick_gives_polar_edge_bound` composes the rational tick check,
the corner-based contact-angle estimate, pairwise separation, and the polar
order argument into one theorem for an individual regular certificate edge.
It assumes the edge's stored lower angle equals its tick divided by 2800 and
that the polar angles are sorted in `[0, 2π]`.

The exceptional tick branches now have corresponding Lean lemmas as well.
`fifteenTickCertificateValid_exactZero_ticks` proves that an exact-origin
endpoint carries tick zero, and `fifteenZeroTick_gives_polar_edge_bound`
handles such a directed edge using only the sorted-angle convention. For a
positive radius whose interval begins at zero,
`fifteenPositiveZeroCosineCap_bounds_or_one` proves that the special cap is
either the trivial value 1 or a valid upper bound on the contact cosine, using
monotonicity on radius boxes bounded by 2. This yields
`fifteenPositiveZeroTick_gives_polar_edge_bound`, including the checker cases
where the cap is at least 1 or at most -1.
The lemmas `fifteenCycleEdgeTickValid_lower_eq` and
`fifteenCycleEdgeTickValid_upper_eq` expose the exact tick-checker inputs
selected by an `L` or `U` edge record. Their regular, positive-zero, and
exact-zero spec lemmas reduce accepted edge records to the corresponding
tick-checker propositions. An `O` edge's tick-zero rule is proved directly.

The cycle parser and validator now also have a proposition-level interface.
`fifteenCycleValid_produces_spec` extracts the parsed edge list from a
successful JSON cycle check and proves every edge-shape and tick check, the
closed-chain data, and the negative integer weight. Given geometric bounds for
those edges, `fifteenCycleValid_excludes_with_edge_bounds` derives the cycle
contradiction without trusting the validator's Boolean result as an opaque
fact. The remaining certificate connection is to derive each geometric edge
bound directly from the parsed edge, its current radial box, and the global
packing hypotheses.

`CirclePacking/FifteenCycleSoundness.lean` proves the generic soundness step
for negative-cycle witnesses. If each checked edge weight is an upper bound
for its polar-angle difference after scaling by 1/2800, then a closed edge
chain cannot have negative total weight. The theorem matches the certificate's
`O`, `L`, and `U` edge conventions to the 17,600-tick upper bound for a full
turn. The remaining connections include deriving the per-edge theorem's
premises from each parsed JSON leaf and lifting the finite Boolean replay to a
proposition about every geometric configuration. The final local obstruction
and its connection to the packing geometry remain outside Lean; the finite
replays alone are not the full optimum proof.

The finite replays are collected in the dedicated target
`CirclePacking.FifteenAllFiniteCertificates`. It combines Stage 0's orbit and
coarse-angle checks, Stage 3 and Stage 4, the exact radial-subdivision tree,
and the residual-pattern handoff. It remains opt-in so the default
`CirclePacking` build does not pay for all 15-disk certificate evaluation.
Build and audit it from this directory with:

```sh
lake build CirclePacking.FifteenAllFiniteCertificates
lake env lean CirclePacking/FifteenTrustAudit.lean
```

The second command runs `#print axioms` on the combined theorem and reports the
actual trust dependencies, including any native-evaluation axiom.

Build the certificate replay with `lake build CirclePacking.FifteenCertificate`
and the analytic tick lemmas with `lake build CirclePacking.FifteenTickSoundness`.
Both are included in the default `CirclePacking` target.

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

`CirclePacking/MainOrderProjection.lean` decodes the two effective masks used
by the main residual cases, enumerates all four local orders per mask, and
proves that both families project to the seven-disk order `(10, 5, 7, 9, 2,
8, 6)`. It also transfers a pairwise angular order on the full sector order
to that core order. `CirclePacking/MainAngleNecessary.lean` proves that the
two geometric barrier expressions are each at most `2π` for a wall-pushed
core in this order, using only pair separation and the complete cyclic angle
sum. The second inequality uses the direct arc from disk 10 to disk 7 while
retaining disk 5 in the packing hypotheses. The Python verifier reports 193
main residual occurrences with these mask types. Exact-root and derivative
formalization, wall-push applicability for every radial leaf, and replaying
the radial tree remain outstanding.

The two alternate nine-circle certificates, their geometric soundness, the
finite P/Q and main-core order projections, the main-order geometric
necessary-angle inequalities, and the rational four-large-disk path-angle
obstruction are replayed by Lean. The exact root and derivative argument,
radial tree, wall-push applicability, and derivation of the required
sector-order hypotheses from the global terminal cases are still checked only
by the Python composition verifier. This remains a partial Lean
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
