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

Build with:

```text
lake update
lake build
```
