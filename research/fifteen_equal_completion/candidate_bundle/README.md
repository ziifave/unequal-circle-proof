# 15 congruent disks: candidate exact global optimality certificate

**Provisional research software. Not independently peer reviewed.**

The files constitute a reproducible computational proof candidate for the best-known 15-equal-disk arrangement in a circle. See `PROOF_SKETCH.md` for the theorem, geometric reductions, exact derivative lemma, computational proof obligations, and caveats. The current replay sends all 760 dihedral classes through the coarse integer angular graph and does not rely on the separate gap-capacity filter in `certify_gap_pruning.py`.

Requires Python 3.10+ (standard library only), GNU C++ compiler with C++17, and a POSIX shell. No floating-point arithmetic participates in any computer-assisted exclusion, though the scripts may print approximate decimal values for convenience.

Run:

```sh
bash run_all.sh
```

This recreates all the intermediate `*.tsv`, numerical bounds and logs; it will fail at any asserted mismatch or unclosed radius box. `verify_coarse_angles.py` checks every positive entry of the fixed 4-type table with exact rational arithmetic. `build_bounds3.py` and `build_bounds4.py` generate refined rational angle tables using a Taylor polynomial with an explicit remainder subtraction; the driver checks exact equality with the embedded C++ tables. `certify_six_nine.py`, `verify_noncanonical_exact.py`, `verify_canonical_exact.py` and `verify_local_constants.py` use Python `fractions.Fraction` or integers for correctness-critical checks.

Expected summary:

- 760 I/O bracelet orbit classes, of which 382 are eliminated by coarse integer negative cycles, leaving 378 for refinement.
- 378 enter finer radial classification; 23 survive the first and 4 survive the second.
- 6I+9O orbit: exactly 3 surviving coarse interval boxes; after a bisection, all 6 leaf boxes close.
- 5I+10O noncanonical orbit A: 47 coarse interval boxes, all closed in 1,641 search nodes.
- 5I+10O noncanonical orbit B: 38 coarse interval boxes, all closed in 646 search nodes.
- 5I+10O canonical orbit: 1,181 coarse interval boxes, 56,573 nodes, 28,846 negative-cycle leaves and 31 leaves in [1.68,1.72]^5.
- Local derivative inequality excludes all those remaining five-radius tuples other than the symmetric candidate, whose tangencies force minimum container radius R0.

The code includes exhaustive search and mathematically justified early-pruning predicates. The accompanying prose is a proof *sketch*, not a substitute for a fully refereed manuscript or an independently checked implementation. Treat any claimed proof of this previously open problem with appropriately high skepticism until independently validated.
