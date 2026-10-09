# Algebraic identification of the ten-circle critical radius

This package compares two definitions of the radius of one fixed contact
configuration of ten circles with radii `sqrt(1), ..., sqrt(10)`: the
geometrically defined critical radius and the isolated real root of an exact
rational polynomial. The manuscript states the certificate bridge required
for that identification. It does not prove that this configuration is
globally optimal among all packings.

The proof documents, exact coefficient tables, scripts, and reproduction data
are in [exact_coefficients_G112](exact_coefficients_G112/README.md). The
associated Lean modules are part of the shared Lean project in the
[global-optimality package](../packing-ten-unequal-circles-in-a-circle/lean/README.md),
under `CirclePacking/G112.lean` and `CirclePacking/P1792.lean`.
