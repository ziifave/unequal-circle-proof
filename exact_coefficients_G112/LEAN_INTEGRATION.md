# Lean integration

`lean/CirclePacking/G112.lean` imports the primitive integer coefficient table
from `circle_G112_primitive_integer_coefficients.tsv`.

The Lean module defines:

- `CirclePacking.g112Basis`, the 16-element radical basis;
- `CirclePacking.g112PrimitiveCoefficients`, the exact 113 by 16 table;
- `CirclePacking.g112PrimitiveEval`, its exact real evaluation;
- `CirclePacking.g112PrimitivePolynomial`, the corresponding `Polynomial ℝ`;
- `CirclePacking.eval_g112PrimitivePolynomial`, identifying polynomial
  evaluation with the finite sum; and
- `CirclePacking.IsG112Root`, the corresponding root predicate; and
- `CirclePacking.G112Compatible`, the explicit bridge to the existing
  Henneberg root definition.

The bridge is intentionally a proposition rather than an unproved theorem:
the archive gives exact elimination and numerical/modular checks, but the
elimination identity has not yet been formalized in Lean.  Thus the existing
`R0` definition remains based on the root-isolation certificate, while the
new algebraic equation is available for a future independently checked
connection theorem.

The package describes a degree-112 polynomial over
`Q(sqrt 2, sqrt 3, sqrt 5, sqrt 7)`.  It does not contain the expanded
degree-1792 rational norm polynomial, so that norm is not yet represented in
Lean.

The Lean theorem `g112_table_shape` checks the 113-row, 16-column shape
inside Lean. An independent replay compares every generated Lean literal with
the primitive TSV and checks that the primitive table is one common nonzero
rational multiple of the exact rational-coefficient TSV. This validates the
transcription and normalization, but does not yet formalize the resultant
computation that produced the coefficients.

## Replay status

- Lean table-shape theorem: passed.
- Characteristic-zero exact coefficients reduced modulo 10391: 1808/1808
  coordinates matched the independent table.
- Independent prime 1129 check: 4 radical embeddings × 9 evaluation points =
  36/36 evaluations passed.
- The 1129 replay requires SymPy for the independent modular eliminant; this
  dependency is used only by the external replay, not by the Lean definition.

The supplementary `degree1792_certificate/` directory contains the
characteristic-zero valuation, degree, interval-root, and finite-field
reports. It defines the rational degree-1792 polynomial as a field norm, but
does not include its expanded coefficient list. The Lean structure
`Degree1792R0Certificate` is therefore an explicit import boundary: once a
concrete rational polynomial and its root/irreducibility proofs are supplied,
`degree1792_root_is_algebraic` derives algebraicity of `R0` immediately.

The attached `circle_exact_eliminant.sage` gives the characteristic-zero
resultant construction, but is explicitly marked as not executed in this
environment. The attached rational interval script was executed and
reproduced the strict endpoint signs and positive derivative on the stated
interval.
