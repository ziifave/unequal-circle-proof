# v4 review and implementation handoff

This is a review and a bounded diagnostic, not a completed exclusion certificate.
The implementation and the existing v4 proof artifacts have not been changed.
The Python diagnostics below were checked with the project environment:

```bash
PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -
```

## Recommended next milestone

Correct the two remaining angle-arithmetic errors, pass the actual radial
constraints to the sector checker, and certify the following small lemma:

> For anchors (4,9) and 7.9 <= R <= 8.303468122111490, disks 7, 8, and 10
> cannot all have their centres in the same closed half-plane bounded by
> the anchor axis.

This lemma matches 12 of the saved v4 frontier boxes. It needs only six
orders, not an enumeration of every order of the other eight disks.
The diagnostic does not replace replay from the initial domain.

## What the saved artifacts actually say

All files listed in the v4 manifest matched their SHA-256 values during review.
The tree contains 36 angular branches, 25 coordinate splits, 10 separation
branches, and 20 discards, with 52 frontier boxes.

`two-anchor-4-9-commonR-v4-box49-difference.json` describes ONE side assignment:

- upper = {1}
- lower = {2,3,5,6,7,8,10}

Its coordinates match frontier entry 49. The reported assignment with all
eight non-anchor disks above the axis is not the assignment in this file.
Thus adding a side split is not necessary to determine box 49's sides.

The current backend derives radial intervals only from coordinate rectangles.
For box 49 this gives 42 zero angle lower bounds among the 45 pairs. Passing
containment upper bounds and necessary radial lower bounds reduces that count
to 33. With the corrected angle function, the first 300 full lower-side
orders were then rejected in a bounded diagnostic.

## Arithmetic corrections still needed

### 1. The numerator of the cosine upper bound

In `proof/angular.py`, `_angle_lower_from_bounds` now selects the upper
denominator when the numerator is negative, but it also substitutes
`numerator_lo`. That does not give an upper bound on the quotient.

Keep the upper numerator in both sign cases:

```python
denominator = denominator_hi if numerator <= 0 else denominator_lo
c = _div(numerator, denominator, ROUND_CEILING)
```

An exact-rational counterexample was reproduced at precision 90 with
`ri = rj = 1` and point radial intervals at:

```text
a = 0.8396396031699210861331862370883458995286148817840877577097477651335248074023405201657183
b = 1.2689987478445456184551770973658692235115578306630285533163876705749029743007422135646209
```

For these values, the v4 quotient is strictly less than the exact rational
`(a*a + b*b - 4)/(2*a*b)`. The quotient using the upper numerator encloses it
from above. Test this with `fractions.Fraction`, independently of the
interval primitives.

### 2. The negative-cosine branch of acos

The comment in `_acos_lower` states the correct identity
`acos(c) = pi - 2*atan(1/z)`, but the return expression computes
`2*pi - atan(1/z)`.

The current function returns approximately 5.75958653158 for `c = -0.5`,
exceeding pi; the actual angle is `2*pi/3`. Use:

```python
return _binary(
    PI_LO,
    _binary(D(2), atan_hi, "*", ROUND_CEILING),
    "-", ROUND_FLOOR,
)
```

With both angle corrections applied only in memory, all six diagnostic
exclusions below still hold. Add independent tests at negative as well as
nonnegative cosine inputs.

### 3. One remaining ordinary Decimal negation

`PackingModel._radial_lower_contract` still uses `-cap` for a negative
coordinate. Replace it with `cap.copy_negate()` and check the boundary-point
case. The earlier correction of the containment contractor did not cover
this separate occurrence.

## Radial information to pass to the backend

Let `U = sup(I_R)` for the current box, and write `s_i = ||p_i||`.
Intersect the Cartesian norm interval with the necessary bounds

\[
\max\{0,\max_{j\ne i}(r_i+2r_j-U)\}\le s_i\le U-r_i.
\]

The lower bound follows from separation and containment of disk j:
`r_i+r_j <= s_i+s_j <= s_i+U-r_j`.
Use outward rounding and treat an empty intersection as a separately
verified contradiction. For the anchors also intersect with `I_R-r_a`
and `I_R-r_b`.

For the lemma, global `U=8.303468122111490` already suffices. Approximate
radial endpoints are:

| Disk | Lower | Upper |
|---|---:|---:|
| 4 | 5.9 | 6.30346812 |
| 7 | 0.66683850 | 5.65771682 |
| 8 | 0.84951432 | 5.47504101 |
| 9 | 4.9 | 5.30346813 |
| 10 | 0.85880953 | 5.14119047 |

These displayed values are explanatory; recompute the full directed
intervals for the certificate.

## Six-order same-half-plane certificate

For disks 7,8,10 and anchor 9, the corrected calculation gives these
conservatively truncated angular lower bounds in radians:

| Pair | Lower bound |
|---|---:|
| 7,8 | 1.0276 |
| 7,10 | 1.1321 |
| 8,10 | 1.1977 |
| 7,9 | 1.0804 |
| 8,9 | 1.1422 |
| 9,10 | 1.2617 |

If all three centres are in one closed half-plane, order them from the
positive anchor axis toward anchor 9. Their intervening gaps, followed by
the gap to anchor 9, have total at most pi. The six necessary lower sums are:

| Order toward anchor 9 | Lower sum |
|---|---:|
| 7,8,10,9 | 3.4870 |
| 7,10,8,9 | 3.4720 |
| 8,7,10,9 | 3.4214 |
| 8,10,7,9 | 3.4102 |
| 10,7,8,9 | 3.3019 |
| 10,8,7,9 | 3.3057 |

Every sum exceeds the rational upper bound `pi < 3.1416`.
Reflection gives the other half-plane. All relevant radial lower bounds
are positive, so their centre directions are defined; the closed-half-plane
formulation includes points on the anchor axis.

At full diagnostic precision, the smallest lower excess over `PI_HI` was
greater than 0.16044128336246319 radians. The corresponding six negative
cycles passed the updated cycle checker, and their stored Decimal edge
sums were also negative under exact Fraction summation.

Saved frontier indices 40 through 51 inclusive all have
`y7.hi <= 0`, `y8.hi <= 0`, and `y10.hi <= 0`. Consequently the lemma is
a candidate closure for all 12 boxes, irrespective of their remaining
side assignments or angular-order facts. Bind each closure to its node
path, not just its mutable array index.

## Implementation order and completion criteria

1. Correct the arithmetic above and add tests against independent exact
   values. Regenerate or rigorously replay the affected search artifacts.
2. Share the necessary radial bounds between the model and the backend;
   preserve the variable-R interpretation of the anchors.
3. Emit this six-order lemma as a reusable certificate. Its verifier must
   recompute the radial and angular bounds and check all six orders.
4. Add a leaf event whose verifier checks the node's same-side condition
   and the lemma's matching anchor/radius assumptions. Integrate it with
   the tree verifier, including a partial-tree mode that reports open leaves.
5. Aim first for the 12 candidate leaves to replay as closed. Recompute the
   remaining frontier count from the resulting tree; do not simply subtract
   12 if regeneration changes the tree.
6. For the remaining boxes, retain this lemma as a filter. Only then assess
   whether side, radial, or sector-order branching gives useful progress.

The existing angular facts concern directions around disk 10's centre;
they are not directly the polar orders around the container centre. Do not
copy them into the sector difference graph without a valid translation.

Status remains UNKNOWN until the relevant tree is fully replayed. This
review closes neither the complete (4,9) branch nor the global optimum proof.
