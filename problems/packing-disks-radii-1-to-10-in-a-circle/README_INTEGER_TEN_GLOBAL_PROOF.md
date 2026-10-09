# Exact computer-assisted optimum: disks of radii 1,...,10 in a circle

## Result

Let

\[
B(R)=\beta_{10,8}(R)+\beta_{8,6}(R)+\beta_{6,7}(R)+\beta_{7,9}(R)+\beta_{9,10}(R),
\quad \beta_{ij}(R)=2\arcsin\sqrt{\frac{ij}{(R-i)(R-j)}}.
\]

The certified optimum is the unique root `R0` of `B(R0)=2*pi` in
`(22.000193012737, 22.000193012738)`, approximately
`22.0001930127373705480969665696`. It matches the Packomania known best
construction. This is a computer-assisted proof with an explicitly declared
trust boundary, not a formal Lean proof or a peer-reviewed result.

## Key idea

The five biggest disks 6..10 form a wall-tangent cycle, in order
`(10,8,6,7,9)` up to reflection. **They do not suffice for a global lower
bound**, as they can all be packed at radius 21.9 in another cyclic order,
`(10,6,9,8,7)`; `check_five_big_witness.py` proves this counterexample
by rational arithmetic.

Instead consider the six-disk subset with radii 5..10. Every feasible packing
of all ten disks restricts to a feasible packing of these six. Enumerate all
60 cyclic orders, up to reflection, using a rational radial-cover tree with
initial radius cap `U=22.00019301274`.

The exact result is:
- 75 tree nodes, 37 splits, 38 leaves;
- 34 leaves: **all** 60 orders ruled out by rational negative-cycle witnesses;
- 4 leaves: all non-core orders ruled out by negative cycles; every order not
  otherwise excluded has core-five projection `(10,8,6,7,9)`. A certified
  radial derivative argument (wall-angle barrier) rules out these.
- Every terminal leaf is closed for `R<R0`, and the tree covers all feasible
  radial vectors at that radius.

An exact upper witness places the five wall disks using the angle-closure
root and the other five disks at rational centers:

```
p1 = (-8.901,  19.006)
p2 = (-15.551,-12.425)
p3 = (12.838,  13.952)
p4 = (11.103,-14.109)
p5 = (-3.357,   1.306)
```

The upper verifier checks 40 non-contact pairs and all remaining containment
constraints using exact rational interval arithmetic.

## Verify

Requires an ordinary CPython 3 environment; no third-party Python modules
are needed to replay the certificate.

```
python3 certify_integer_ten_global.py
```

Individual tests:

```
python3 verify_ten_upper.py
python3 verify_ten_global_tree.py
python3 check_five_big_witness.py
```

`-O` and `-OO` modes are explicitly rejected because the verifier's
assumptions are enforced partly by Python `assert` statements.

`gen_ten_global_tree.py` is **untrusted proof discovery code**; it uses
floating-point routines to suggest angle ticks. All accepted data, rational
cover relations, and angular/differential inequalities are independently
rechecked by `verify_ten_global_tree.py`.

## Contents

- `optimal_ten_integer_disks.pdf`: 5-page mathematical manuscript with diagram.
- `optimal_ten_integer_disks.tex`: TeX source.
- `certify_integer_ten_global.py`: single-command end-to-end replay.
- `verify_ten_upper.py`: exact root and ten-disk witness.
- `verify_ten_global_tree.py`: exact global lower-bound verifier.
- `ten_global_proof_tree.json`: finite proof certificate (data).
- `gen_ten_global_tree.py`: optional certificate discovery/regeneration.
- `check_five_big_witness.py`: verifies the five-largest-disks counterexample.

## Trust boundary

The certificate is not itself a formal proof in a proof assistant. The claim
is conditional on the correctness of the mathematical rules as implemented in
these Python checkers, on correct unoptimized interpreter execution,
`fractions.Fraction`, integer square-root and Taylor-bound identities, and
unchanged certificate inputs. The independent mathematical or code audit and
newness/prior-art investigation remain open.

Source for the known construction: [Packomania, radii i](https://packomania.com/ccin/ccin.html), updated September 10, 2026.
