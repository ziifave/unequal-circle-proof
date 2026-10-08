# Exact global optimality for ten unequal circles

This repository contains a computer-assisted proof that the smallest radius
of a circular container holding ten pairwise non-overlapping circles of
radii $1,\sqrt2,\ldots,\sqrt{10}$ is the exact number $R_{\mathrm{crit}}$
defined by two angular equations. The certified enclosure is

```text
8.303468122111489 <= R_crit < 8.303468122111490
```

The lower bound is a complete rational radial and angular case analysis. Its
remaining cases are closed by a seven-circle angle barrier and exact
negative-cycle certificates for the exceptional orders. A matching ten-circle
configuration proves attainability. The case tree covers radii up to its
certified cap; the exclusion rules rule out every packing with radius below
`R_crit`, while the constructed packing exists at `R_crit`. The proof and its
computational trust boundary are described in the [English manuscript](paper/main.pdf), with
source at [paper/main.tex](paper/main.tex).

## Reproduce the proof

From this directory, with `uv` installed:

```bash
uv run --locked python tools/verify_global_optimality_completion.py
```

The replay writes
`artifacts/global-optimality-completion-2026-10-09.json`, including the input
SHA-256 manifest. The checker requires ordinary Python execution; it refuses
`-O` and `-OO`, which would disable assertions in component verifiers. The
certificate and report are fixed together with the manuscript in the Git
commit containing this release.

Build the PDF with the bundled Tectonic executable:

```bash
./tools/bin/tectonic --keep-logs --outdir paper paper/main.tex
```

This is a computer-assisted proof, not an end-to-end theorem-prover
formalization. Its trust boundary includes the replay code, Python's exact
integer and rational arithmetic, and the hashed certificate inputs; the
manuscript states the checks that connect the finite records to the geometric
claims.
