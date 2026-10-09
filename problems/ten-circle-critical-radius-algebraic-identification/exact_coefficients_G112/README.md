# From external exact arithmetic to Lean

This directory contains the reproducible arithmetic boundary for the
algebraic radius associated with the selected contact configuration of the
ten unequal circles with radii `r_i = sqrt(i)`. It is important to keep the
scope precise:

> The computation identifies and checks an algebraic equation for one
> isolated contact-configuration radius. By itself it does not prove that
> the configuration is the global optimum of the packing problem.

The workflow has two layers. The external layer performs large exact
arithmetic tasks that are inconvenient to replay directly in Lean. The Lean
layer imports the resulting finite data and states the exact logical bridge
from the contact equations to the polynomial root and algebraicity claims.

## Workflow

```text
contact geometry
      │
      ▼
Sage / exact rational and multiquadratic arithmetic
      │  resultants, content factors, degree bounds
      ▼
finite-field checks and exact coefficient reconstruction
      │  modular interpolation, Rabin tests, conjugate checks
      ▼
P1792 coefficient table + rational root interval certificate
      │  attached files, SHA-256 manifest
      ▼
Lean imports the literal coefficient table
      │
      ├─ checks table shape and polynomial evaluation definitions
      ├─ accepts a supplied contact-elimination bridge
      └─ derives P1792(R₀)=0 and algebraicity from supplied certificates
```

The arrows are deliberately not all formalized in the same system. An
external report or a hash is evidence for a computed artifact, not a Lean
proof term. The Lean theorems expose the exact assumptions needed at the
boundary, so later work can replace an external assumption with a Lean replay
theorem without changing the downstream statements.

## 1. Contact equations and the degree-112 eliminant

The contact pattern is encoded in
`degree1792_certificate/unequal_circles_elimination_spec.md` and the
corresponding Sage/Python programs. In outline:

1. Express outer tangencies and circle-circle tangencies using cosine
   variables over `K = Q(sqrt(2), sqrt(3), sqrt(5), sqrt(7))`.
2. Build the angular-chain polynomials `P2`, `P3`, `P4` by resultants.
3. Build the rigid-triangle closure polynomial `H`.
4. Form `F(R) = Res_w(P4, H)`.
5. Prove or verify the characteristic-zero content factors and divide them
   out to obtain the degree-112 polynomial `G(R) in K[R]`.

The characteristic-zero valuation and degree arguments are documented in
`circle_degree1792_proof_report.md`. The scripts
`circle_content_lower_bounds.py`, `circle_local_field.py`, and
`circle_degree_leading_mod.py` support those checks. The Sage construction
is in `degree1792_certificate/circle_exact_eliminant.sage`.

The exact coefficient package contains both the monic field coefficients and
the primitive integer normalization:

- `circle_G112_exact_coefficients.tsv` — exact coefficients in the 16-element
  radical basis;
- `circle_G112_primitive_integer_coefficients.tsv` — the primitive integer
  coefficient table;
- `circle_G112_exact_expanded.txt` — expanded human-readable expressions.

## 2. From `G` to the degree-1792 rational polynomial

The 16 sign embeddings of `K` give 16 conjugate degree-112 polynomials.
Their product, equivalently the field norm of the monic `G`, is a rational
polynomial of degree `16 * 112 = 1792`. The complete primitive integer
coefficient list is stored in the attached algebraic reproducibility data and
is represented in Lean by [`P1792.lean`](../../packing-ten-unequal-circles-in-a-circle/lean/CirclePacking/P1792.lean) as
`p1792PrimitivePolynomial : Polynomial Q`.

The external verification package checks:

- exact coefficient tables modulo independent primes;
- the P1792 norm coefficient table and its normalization;
- pairwise coprimality of the 16 conjugates modulo a good prime;
- the degree-112 irreducibility test via Rabin's criterion;
- the rational root interval by exact integer endpoint signs;
- uniqueness on the interval using the derivative/Taylor certificate; and
- the SHA-256 manifest of the supplied artifacts.

The main replay entry point is the Python verification bundle in
`degree1792_certificate/`. The bundled smoke test runs the exact
characteristic-zero, finite-field, and interval checks:

```bash
cd exact_coefficients_G112/degree1792_certificate
uv run --with sympy python circle_degree1792_smoketest.py
```

The coefficient-table replay is run separately with
`python exact_coefficients_G112/verify_G112_exact.py` after regenerating the
coefficient table at the path expected by that script. The reports in this
directory record the inputs and expected checks.

## 3. The real root interval

`degree1792_certificate/circle_radius_root_interval_certificate.py` works
with rational/integer directed bounds. It certifies strict endpoint signs
for the real closure equation and a positive derivative bound on the stated
interval. Therefore the closure equation has exactly one root in that
interval.

This proves uniqueness of the selected real contact branch, not global
optimality. The geometric elimination argument must still establish that
the selected branch satisfies the contact equations and that its radius is
the root being discussed.

## 4. Lean integration

The Lean side is intentionally small and exact:

- [`G112.lean`](../../packing-ten-unequal-circles-in-a-circle/lean/CirclePacking/G112.lean) contains the field-basis coefficient table
  and the degree-112 polynomial interface.
- [`P1792.lean`](../../packing-ten-unequal-circles-in-a-circle/lean/CirclePacking/P1792.lean) contains the 1793 integer coefficients,
  the rational polynomial, evaluation lemmas, and the P1792 certificate
  interface.
- `LEAN_INTEGRATION.md` records the detailed import
  boundary and current audit status.

The key structure is `ContactEliminationBridge`. It packages the exact
logical fact that the chosen contact realization gives a root of the G112
eliminant and that the G112 root gives a root of P1792. From such a bridge,
Lean derives the polynomial-root statement through
`p1792_root_of_elimination_bridge`.

`P1792R0Certificate.toDegree1792` then converts supplied nonzero, degree, and
irreducibility facts into the existing `Degree1792R0Certificate` interface.
The coefficient literals and polynomial evaluation are checked by Lean; the
large resultant computation, finite-field arithmetic, and interval search
remain external inputs until separately replayed/formalized.

Build the Lean module from the Lean project directory with:

```bash
cd lean
lake env lean CirclePacking/P1792.lean
```

## 5. What is proved at each boundary

### External arithmetic

The external scripts provide exact integer/rational calculations, modular
cross-checks, and a reproducible root interval certificate. These are
replayable computational claims, with source files and hashes recorded in
the certificate bundle.

### Lean

Lean checks the imported coefficient data and proves the downstream algebraic
implications from explicitly supplied hypotheses. In particular, Lean can
assemble:

```text
contact-elimination bridge
        + P1792 nonzero/degree/irreducibility data
        ───────────────────────────────────────────
        P1792(R₀) = 0 and IsAlgebraic Q R₀
```

This separation avoids treating a log file, a decimal approximation, or a
hash as if it were itself a theorem. The remaining formalization target is
to turn the characteristic-zero eliminant identities, finite-field
certificates, and interval/root-isolation certificates into independently
checked Lean propositions (or verified certificate replayers).

## 6. Reproducibility and limitations

The certificate package should be treated as immutable input: changes to
coefficient tables or scripts require regenerating the manifest and rerunning
the checks. The current proof objects establish algebraic facts about the
selected contact branch. They do **not** yet establish

```text
R* = R0
```

for the full ten-circle packing problem. A global optimality proof still
needs a complete exclusion of every packing with `R < R0`, including contact
patterns not represented by this eliminant.
