# Stage 4 certificate replay

The Stage 4 producer writes a prefix-tree certificate for each of the 19
`CLOSED` patterns in the Stage 4 manifest. The Lean checker validates all 12
children of each split, checks every structural-pruning leaf, and replays the
recorded negative cycles from their edge topology using the Stage 4 integer
tick table. It does not rerun Bellman–Ford.

The manifest check verifies that all 23 Stage 4 inputs are exactly the 23
`UNKNOWN` patterns in the Stage 3 manifest, and that the 19 replayed closures
are exactly the `CLOSED` rows. The four remaining patterns are retained for
the local analysis.

Build the Stage 4 replay alone with:

```sh
lake build CirclePacking.FifteenStage4
```

Build the combined Stage 3 and Stage 4 finite-certificate result with:

```sh
lake build CirclePacking.FifteenStages34Integrated
```

The four residual patterns are connected to the exact radial-subdivision
certificate in `CirclePacking.FifteenStage4LocalHandoff`. This checks the
three I5/O10 roots (47, 38, and 1,181 boxes) and the I6/O9 special pattern,
including that the local box is exactly `[42/25, 43/25]` in each inner radius.
The same theorem bundles the Stage 3, Stage 4, and radial-certificate replay
results:

```sh
lake build CirclePacking.FifteenStage4LocalHandoff
```

`CirclePacking.FifteenLocalBarrierAlgebra` formalizes the calculus-free core
of the local argument: the max-of-two-slopes estimate, the alternating
five-cycle identity and its indexed L1 consequence, the quadratic error bound,
and the rational margin `29/500`. These facts do not yet establish the
derivative bounds or Taylor inequalities for the geometric angle function.
The local analytic and geometric connection remains open.

The first packing-to-certificate soundness slice is in
`CirclePacking.FifteenPackingGeometry`. From the `Packing` containment and
separation fields it derives the center-radius bound `‖cᵢ‖ ≤ R - 1`, the
pairwise radial inequality, and the necessary upper-endpoint condition
`2 ≤ uᵢ + uⱼ` for any radial box containing two distinct unit-disk centers.
Consequently a `SUM` terminal condition with `uᵢ + uⱼ < 2` is impossible for
an actual unit-disk packing. It also proves that at most one center can have
radius below 1, that a center at the origin forces every other center to have
radius at least 2, and the corresponding exclusion for two radial boxes whose
upper endpoints are below 1. These are geometric ingredients for the small
count and origin pruning rules. Build this geometry layer with:

```sh
lake build CirclePacking.FifteenPackingGeometry
```

This closes the geometric meaning of the pair-sum leaf and formalizes the
basic implications behind subunit-count and origin pruning. Deriving
certificate box membership and signed edge bounds for every cycle leaf, and
connecting the remaining Stage 3/4 structural pruning predicates to the
packing model, remain separate obligations.

`CirclePacking.FifteenTickSoundness` now also proves regular tick lower bounds
for every branch of the checker, including zero ticks and the half-turn tick;
it no longer assumes the rational cosine cap is already in the Taylor branch.
`CirclePacking.FifteenPackingPolarCoordinates` extracts polar coordinates for
each center of an arbitrary packing, transfers unit-disk separation to those
coordinates, and proves the radius-swap identity needed for backward (`L`)
edges. The final cycle connection still needs the sorted reindexing and the
per-edge assembly from these bounds and the radial-box membership data.

Build these geometric interfaces with:

```sh
lake build CirclePacking.FifteenTickSoundness
lake build CirclePacking.FifteenPackingPolarCoordinates
```

Regenerate the Stage 4 certificate data with:

```sh
python3 tools/export_lean_stage4_certificates.py
```

This formalizes finite certificate replay, the manifest handoff, and part of
the arithmetic local barrier. It does not yet prove in Lean that every checked
pruning predicate follows from the geometric packing model, nor does it close
the four residual cases with the local analytic argument. Those soundness and
final-analysis layers remain separate obligations.
