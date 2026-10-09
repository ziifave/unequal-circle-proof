# 15 congruent disks: candidate exact global optimality certificate

**Provisional research software. Not independently peer reviewed.**

The files constitute a reproducible computational proof candidate for the best-known 15-equal-disk arrangement in a circle. See `PROOF_SKETCH.md` for the theorem, geometric reductions, exact derivative lemma, computational proof obligations, and caveats. The current replay sends all 760 dihedral classes through the coarse integer angular graph and does not rely on the separate gap-capacity filter in `certify_gap_pruning.py`.

Requires Python 3.10+ (standard library only), GNU C++ compiler with C++17, and a POSIX shell. No floating-point arithmetic participates in any computer-assisted exclusion, though the scripts may print approximate decimal values for convenience.

Run:

```sh
bash run_all.sh
```

This recreates all intermediate `*.tsv`, certificates, numerical bounds and logs; it will fail at any asserted mismatch or unclosed radius box. `verify_coarse_angles.py` checks every positive entry of the fixed 4-type table with exact rational arithmetic. `build_bounds3.py` and `build_bounds4.py` generate refined rational angle tables using a Taylor polynomial with an explicit remainder subtraction; the driver checks exact equality with the embedded C++ tables. `check_stage0_certificate.py` independently checks all 760 binary dihedral classes and the full radial-type assignment coverage and cycle witnesses for every excluded class. `certify_six_nine.py`, `verify_noncanonical_exact.py`, `verify_canonical_exact.py` and `verify_local_constants.py` use Python `fractions.Fraction` or integers for correctness-critical checks.

Expected summary:

- 760 I/O bracelet orbit classes, of which 382 are eliminated by coarse integer negative cycles, leaving 378 for refinement.
- `stage0_certificate.json.gz` records a negative-cycle witness for every structurally admissible radial-type assignment of each excluded class. The separate checker regenerates all 760 binary classes, checks complete assignment coverage and verifies each cycle using integer arithmetic.
- 378 enter finer radial classification; 23 survive the first and 4 survive the second.
- 6I+9O orbit: exactly 3 surviving coarse interval boxes; the positive-radius halves and separate exact-origin case give 9 certified leaves.
- 5I+10O noncanonical orbit A: 47 coarse interval boxes, all closed in 1,641 search nodes.
- 5I+10O noncanonical orbit B: 38 coarse interval boxes, all closed in 646 search nodes.
- 5I+10O canonical orbit: 1,181 coarse interval boxes, 56,573 nodes, 28,846 negative-cycle leaves and 31 leaves in [1.68,1.72]^5.
- Local derivative inequality excludes all those remaining five-radius tuples other than the symmetric candidate, whose tangencies force minimum container radius R0.
- `make_exact_certificate.py` serializes the 1,266 fine-subdivision trees plus the nine 6+9 endpoint leaves to `exact_subdivision_certificate.json`. `check_exact_certificate.py` independently checks their splits, rational angular edge weights, negative cycles, pair-sum exclusions, local-box leaves, and that the three 6+9 special assignments equal those in `full_residuals.txt`. Stages 3 and 4 and the radial-box enumerator remain exhaustive replay steps checked through exact counts, identities, and uniqueness assertions.

The code includes exhaustive search and mathematically justified early-pruning predicates. The accompanying prose is a proof *sketch*, not a substitute for a fully refereed manuscript or an independently checked implementation. Treat any claimed proof of this previously open problem with appropriately high skepticism until independently validated.

## Lean replay of Stage 3 closures

`tools/export_lean_stage3_certificates.py` regenerates 355 compact pruning
certificates for the patterns marked `CLOSED` in `stage3.tsv`. It invokes the
C++ producer only to create certificate data, then interns repeated negative
cycle edge lists in per-pattern dictionaries. Lean checks every prefix-tree
split and leaf, recomputes each referenced cycle's integer edge weights, and
checks strict negativity. The aggregator also verifies that the 378 Stage 3
rows are exactly the Stage 0 survivor patterns, that 355 rows are certified,
and that the remaining 23 rows are passed onward.

Run the replay with:

```sh
python3 tools/export_lean_stage3_certificates.py
cd problems/packing-disks-radii-sqrt1-to-sqrt10-in-a-circle/lean
lake build CirclePacking.FifteenStages34
```

This closes the finite Stage 3 certificate replay only. The Lean cycle checks
still use `native_decide`, and the geometric soundness theorem connecting the
Stage 3 pruning predicates and angle table to arbitrary disk packings, the
Stage 4 certificates, and the final local analysis remain separate obligations.
