# Algebraic candidate radius for 10 unequal circles — reproducibility bundle

**Scope:** Candidate configuration with radii `sqrt(1), ..., sqrt(10)` and outer
radius near `8.3034681221114890787043811875161993...`.

This archive includes the exact coefficient data and **source code actually used
in the preceding computation**, with all inputs inside the archive. It does not
contain a Lean formalization, and **does not prove global optimality** of the
packing. The notes under `notes/` include historical, not independently audited
claims: do not treat those notes as machine-checked proof certificates.

## Files

- `data/G112_monic_components.tsv`: powers 0 through 112, each with 16
  rational basis coordinates for the monic degree-112 polynomial over
  `K = Q(sqrt(2),sqrt(3),sqrt(5),sqrt(7))`.
- `data/G112_primitive_components.tsv`: same `K`-polynomial multiplied by a
  scalar so all 16 basis coordinates are primitive integers. **This is not** a
  polynomial with rational/integer coefficients in `R` alone.
- `data/P1792_primitive_integer_coefficients.tsv`: all 1793 integer coefficients
  of a primitive degree-1792 polynomial over `Q`, ascending degree from 0 to
  1792. Derived by taking the field norm of the 112-degree `K` polynomial.
- `data/G112_mod10391_reference.json`: independent modular reference data.
- `SHA256SUMS`: cryptographic hashes of all four input/output data files.
- `scripts/exact_coeffs_quotient_omp.cpp`: characteristic-zero construction of
  the 112-degree `K` polynomial from 113 exact resultant quotient evaluations.
- `scripts/normalize_G_primitive.py`: derive integer 16-basis coordinates from
  monic rational coordinates.
- `scripts/expand_norm.cpp`: GMP-based field norm by conjugate-pair products,
  extracting primitive integer coefficients.
- `scripts/verify_G112_exact.py`: reduce all 1808 rational coordinates modulo
  10391 and compare with the reference.
- `scripts/check_norm_mod.py`: independently multiply 16 conjugates modulo
  two split primes; checks all 1793 coefficients, plus coprimality and
  irreducibility tests modulo 10391.
- `scripts/check_P_root_interval.py`: pure-integer sign and uniqueness check
  for a `P1792` root in the stated rational interval.
- `scripts/circle_radius_root_interval_certificate.py`: rational interval and
  outward square-root rounding for the **contact closure equation**, independent
  of the univariate polynomial.
- `notes/`: derivation, provisional historical proof discussion, and prior run
  logs; these are supporting research records, not formal proof objects.
- `exploratory/`: older exploratory scripts and an unexecuted SageMath sketch.

## Basis ordering

`basis_m`, with `0 <= m < 16`, corresponds to the monomial radical

```
(√2)^(m&1) (√3)^((m>>1)&1) (√5)^((m>>2)&1) (√7)^((m>>3)&1).
```

## Reproduce the existing witnesses (fast checks)

From the directory created when extracting this archive:

```bash
python3 -m pip install sympy
./verify.sh
sha256sum -c SHA256SUMS
```

This runs exact arithmetic checks (including modular finite fields); `Decimal`
formatting in the interval script only displays rational bounds and is **not**
used to make assertions.

## Regenerate polynomial coefficients (can be computationally expensive)

Requires `g++`, `libgmp-dev`, `libgmpxx`, an OpenMP-enabled compiler, and
Python 3 with SymPy. On Debian/Ubuntu, GMP's C++ headers are provided by
`libgmp-dev`.

```bash
./reproduce.sh
```

The script compiles two C++ sources, recomputes all 113 exact evaluations,
interpolates the `K`-polynomial, converts it to primitive basis coefficients,
and recomputes the degree-1792 primitive norm. It checks byte-level equality
against the included tables. It uses only relative paths, with no `/mnt/data`
inputs. The exact `G112` interpolator is far more expensive than the norm.

To regenerate just `P1792` from the supplied exact `G112` coefficients:

```bash
g++ -O3 -std=c++17 scripts/expand_norm.cpp -o expand_norm -lgmpxx -lgmp
./expand_norm data/G112_primitive_components.tsv P1792_recomputed.tsv
cmp P1792_recomputed.tsv data/P1792_primitive_integer_coefficients.tsv
```

To see the content hash of the rational-coefficient polynomial TSV:

```bash
sha256sum data/P1792_primitive_integer_coefficients.tsv
```

## Strict proof boundaries

1. The integer polynomial `P1792` has been reproduced independently from the
   bundled `K`-coefficient input and checked modulo 10391 and 1129.
2. The provided scripts separately isolate **a root of `P1792`** and
   **a root of the contact-closure equation** within the same rational interval.
   **The resultants and extraneous-factor arguments connecting these roots
   have not been formalized in Lean.** They require independent checking of
   the geometry-to-polynomial identity. Shared intervals alone do not prove
   two functions share the same root.
3. The historical interpolation routine uses 113 exact evaluations plus three
   held-out points. Alone, these evaluations are not a proof that the quotient
   is globally a polynomial of degree 112; the symbolic divisor/degree
   arguments in `notes/` need separate verification.
4. These computations concern a candidate contact configuration. They do not
   establish that this packing is globally optimal.

For formalization, the safest starting point is to define `P1792` directly
from the integer TSV, then prove its root using a certified algebraic
elimination theorem connecting the closure equation to `P1792`.
