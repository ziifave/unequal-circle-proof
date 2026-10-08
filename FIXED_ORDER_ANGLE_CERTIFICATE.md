# Fixed-order all-pair angular certificate

This certificate strengthens the root-level angular cut for the seven-circle
subset `{4,5,6,7,8,9,10}`. It does not assume a contact graph.

For every pair of circles, directed interval arithmetic computes a certified
lower bound `alpha_ij` on the angle between their center rays. For a cyclic
order of the seven rays, let `x_0,...,x_6` be the seven nonnegative angular gaps.
For every unordered pair of positions, both directed paths around the cycle
give valid inequalities

```text
sum_{g in path} x_g >= alpha_ij.
```

For a fixed order, write these 42 path inequalities as `q_k . x >= b_k`.
The certificate stores nonnegative Farkas multipliers `y_k` satisfying

```text
sum_k y_k q_k[g] <= 1       for every gap g.
```

Consequently every feasible gap vector would satisfy

```text
sum_k y_k b_k <= sum_g x_g = 2*pi.
```

Thus `sum_k y_k b_k > 2*pi` is a contradiction. SciPy is used only by the
discovery script to find multipliers; the replay verifier uses no SciPy and
checks the column inequalities, directed-rounded angle bounds, and the strict
margin against an upward bound for `2*pi`.

## Certified result

At `rho=7.9`, all 46,080 radial boxes (360 cyclic orders times 2^7 radial
subboxes) pass in the MPFI replay:

```text
MPFI radial-partition replay: PASSED (46080 cells)
```

The certificate stores outward-rounded radial-box endpoints and Farkas
multipliers discovered with SciPy, rounded inward to decimal values. MPFI
recomputes every box's corner angle lower bounds, the column inequalities, and
the strict comparison with an upward-rounded `2*pi`. The boxes cover the full
root radial intervals, so this is stronger than treating the seven radial
coordinates as independent in one large box. Therefore, conditional on the
MPFI replay kernel,
the seven-circle subset is infeasible at this radius. Every ten-circle packing
contains this subset, so the certified lower bound is

```text
R* >= 7.9.
```

Machine-readable certificate:
`certificates/fixed-order-radial-partition7-mpfi-7.9.dat.gz`

Replay:

```bash
cc -O2 -std=c11 -DN=7 -DSTART=4 mpfi/radial_partition_replay.c \
  -lmpfi -lmpfr -lgmp \
  -o fixed_order_replay
gzip -dc certificates/fixed-order-radial-partition7-mpfi-7.9.dat.gz | \
  ./fixed_order_replay -
```

An independent structural audit is also available:

```bash
python3 mpfi/audit_partition_certificate.py \
  certificates/fixed-order-radial-partition7-mpfi-7.9.dat.gz \
  --rho 7.9 --start 4 --n 7 --split 2
```

It checks the 360 order representatives, the 128 boxes per order, and the
coverage of every radial interval separately from the MPFI inequality replay.

This is an implementation-conditional computational certificate, not a proof
formalized in a proof assistant. It proves exclusion at the displayed radius
and, by monotonicity, at every smaller radius; it does not establish `R*=R0`.

For the global completion, the same 46,080-cell lower-bound certificate is now
also replayed by the exact-rational verifier
[`tools/verify_fixed_order_rational_certificate.py`](tools/verify_fixed_order_rational_certificate.py).
That verifier uses MPFI data only as rational interval endpoints; all angle,
Farkas, and \(2\pi\) comparisons are checked with `Fraction` arithmetic. The
global completion and its scope are documented in
[`GLOBAL_OPTIMALITY_COMPLETION_2026-10-09.md`](GLOBAL_OPTIMALITY_COMPLETION_2026-10-09.md).
