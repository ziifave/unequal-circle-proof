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

Regenerate the Stage 4 certificate data with:

```sh
python3 tools/export_lean_stage4_certificates.py
```

This formalizes finite certificate replay and the manifest handoff. It does
not yet prove in Lean that every checked pruning predicate follows from the
geometric packing model, nor does it close the four residual cases with the
local analytic argument. Those soundness and final-analysis layers remain
separate obligations.
