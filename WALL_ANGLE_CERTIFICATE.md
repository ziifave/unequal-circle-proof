# Exact wall-contact angular cut

For a circle `i` touching the container wall, its center radius is exactly
`R-r_i`.  Therefore a wall-contact pair has the certified angular lower bound

```text
acos(1 - 2*r_i*r_j / ((R-r_i)*(R-r_j))).
```

The scripts `tools/wall_angle_certificate.py` and
`tools/verify_wall_angle_certificate.py` use all directed path inequalities for
each cyclic order and a nonnegative Farkas certificate.  The discovery script
uses SciPy only to find multipliers; the verifier is SciPy-free.

The cut is monotone in `R`: evaluating it at the target upper radius `R0` is
the weakest test on the interval `R <= R0`.  Thus a certified rejection at
`R0` rejects the same wall set throughout the whole lower-bound interval.

As an audit, the cut was evaluated at `R0` on all 16 wall sets appearing in
the completed `m=5` generic topology artifact, all 42 wall sets appearing in
the completed `m=6` artifact, and the known seven-circle core wall set
`{2,5,6,7,8,9}`.  No set was rejected.  This is a valid negative result: the
wall-only angular condition is not strong enough by itself at `R0` for these
cases, but it remains available as a proof-safe upper-level filter for larger
support sizes and partial topology nodes.
