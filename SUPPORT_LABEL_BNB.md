# Support-label branch-and-bound

`tools/support_label_branch_bound.py` is the first upper-level search layer
that branches on radius-label domains before introducing geometry variables.
It starts from a rooted topology and maintains a domain of possible labels for
each circle vertex.  A node is rejected only by directed radius-only angular
necessary conditions:

- `LOCAL_ANGLE_FAIL`: a local neighbor cyclic-order lower bound exceeds
  `2*pi` for every possible label assignment;
- `WALL_ANGLE_FAIL`: the exact wall-contact angular lower bound has the same
  contradiction;
- `DIAMOND_OVERLAP`: a four-circle two-anchor motif has no separated
  intersection-sign branch under the assigned radii;
- `LABEL_DOMAIN_EMPTY`: no injective label remains.

An unresolved complete label assignment is recorded as `UNRESOLVED_LEAF`; it
is never discarded merely because a floating-point or nonlinear solver failed.
This is therefore a proof-safe ledger, although it is not yet the complete
geometry proof: unresolved leaves still require interval contact/stress solving
and extension feasibility.

For a smoke-test run on the first five `m=5` rooted topologies:

```text
LOCAL_ANGLE_FAIL   6,450
WALL_ANGLE_FAIL        0
DIAMOND_OVERLAP        0
UNRESOLVED_LEAF   141,000
```

The artifact is `artifacts/support-label-bnb-m5-first5.json`.  The large
unresolved count is expected at this stage and identifies the next work: share
partial-angle calculations across topology nodes and add the all-pair local
angular LP before any nonlinear solver is called.  The diamond layer is already
implemented, but does not reject any of this first-five-topology smoke test.

The independent micro-DAG audit was then extended over all 106 classified
topologies, with prefixes of up to six added vertices, at most 200 construction
sequences and 32 motifs per topology.  It produced:

```text
MICRO_DAG_FAIL        0
UNRESOLVED          106
```

This is again a negative strength result, not a soundness failure.  The
interval motifs tested so far do not certify impossibility for any complete
topology.  The full detailed run is intentionally kept out of the repository;
the reproducible ledger summary is
`artifacts/micro-dag-filter-prefix6-summary.json`.
