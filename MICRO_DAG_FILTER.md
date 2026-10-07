# Small Henneberg-I motif filter

`tools/micro_dag_filter.py` extracts a short prefix of an Henneberg-I
construction with the wall center `O` as a base and treats any unused edge
inside the prefix as a closure edge.  For every sign branch it evaluates the
closure residual over

```text
[7.7997, 8.3034681221114890787043811875...].
```

A branch is discarded only when an intersection radicand is certified
negative or the closure residual interval excludes zero.  A motif is marked
`MICRO_DAG_FAIL` only when all of its sign branches are discarded.  Numerical
root non-discovery is never used as a rejection reason.

The first audit over the existing 106 Henneberg-classified graphs, using
prefixes of at most four added vertices, produced:

```text
MICRO_DAG_FAIL  0
UNRESOLVED    106
```

This is a negative strength result, not a failure of soundness.  The next
refinement is to use five- and six-vertex prefixes and choose motifs by closure
count before interval evaluation.

That refinement has now been run over all 106 topologies with
`--max-prefix 6 --max-sequences 200 --max-motifs 32 --r-slices 1`.  The ledger remained:

```text
MICRO_DAG_FAIL  0
UNRESOLVED    106
```

Thus the current motif family is proof-safe but not yet strong enough to reject
a topology.  The next useful refinement is to rank by the number of independent
closure edges, subdivide the R interval before evaluating residuals, and use
exact local label assignments inside a motif.  The small reproducible summary
is `artifacts/micro-dag-filter-prefix6-summary.json`; the large per-branch
trace is deliberately not versioned.
