#!/usr/bin/env bash
# Recreate all coefficient tables from geometry, using exact rational and integer arithmetic.
# NOTE: the 113 exact evaluations can be computationally intensive.
set -euo pipefail
cd "$(dirname "$0")"
: "${CXX:=g++}"
"$CXX" -O3 -std=c++17 -fopenmp scripts/exact_coeffs_quotient_omp.cpp -o ./exact_G112_generator -lgmpxx -lgmp
"$CXX" -O3 -std=c++17 scripts/expand_norm.cpp -o ./expand_norm -lgmpxx -lgmp
# Generated files are compared to the bundled witnesses; originals are never overwritten.
./exact_G112_generator ./G112_recomputed.tsv
cmp ./G112_recomputed.tsv data/G112_monic_components.tsv
cp data/G112_primitive_components.tsv ./G112_primitive_reference.tsv
python3 scripts/normalize_G_primitive.py
cmp data/G112_primitive_components.tsv ./G112_primitive_reference.tsv
./expand_norm data/G112_primitive_components.tsv ./P1792_recomputed.tsv
cmp ./P1792_recomputed.tsv data/P1792_primitive_integer_coefficients.tsv
./verify.sh
