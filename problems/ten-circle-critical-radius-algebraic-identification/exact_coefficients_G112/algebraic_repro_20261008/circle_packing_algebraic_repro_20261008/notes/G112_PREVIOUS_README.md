# 10 unequal circles: exact characteristic-zero polynomial G(R)

**Result (2026-10-08).** For radii `r_i = sqrt(i), i=1,...,10`, the circle-core contact equations used in the previous investigation yield an exact polynomial

\[
G(R)=R^{112}+\sum_{j=0}^{111}a_jR^j,\qquad a_j\in K=\mathbb Q(\sqrt2,\sqrt3,\sqrt5,\sqrt7).
\]

This package contains all 113 coefficients in the integral-basis-style monomial radical representation. It refers to a *candidate configuration* and does not prove packing global optimality.

## Coefficient files

- `circle_G112_exact_coefficients.tsv`: the **exact monic** coefficients. Each row `power=j` and `basis_m=b` is the rational coefficient in front of `R^j * product(sqrt(2),sqrt(3),sqrt(5),sqrt(7))`, where `m` is the 4-bit mask of factors in the displayed order. Fractions are exact `numerator/denominator`.
- `circle_G112_primitive_integer_coefficients.tsv`: same polynomial multiplied by its **common primitive integer multiplier**, all coefficients integers. Monic and primitive forms have exactly the same zeros.
- `circle_G112_exact_expanded.txt`: mathematically explicit 113 coefficient expressions, one per degree. Large numbers are unavoidable; this text is ~1.9 MB.

Basis `m=0..15`: `1`, `sqrt(2)`, `sqrt(3)`, `sqrt(6)`, `sqrt(5)`, `sqrt(10)`, `sqrt(15)`, `sqrt(30)`, `sqrt(7)`, `sqrt(14)`, `sqrt(21)`, `sqrt(42)`, `sqrt(35)`, `sqrt(70)`, `sqrt(105)`, `sqrt(210)`.

## Derivation and computation

Let `P4(R,w)` be the eighth-degree cosine-chain eliminant, and `H(R,w)` the fourth-degree triangle closure eliminant from the earlier elimination specification. Define

\[
F(R)=\operatorname{Res}_w(P_4(R,w),H(R,w)),\quad
D(R)=(R+\sqrt{10})^{16}\prod_{i\in\{2,5,6,7,8,9\}}(R-\sqrt i)^{32}.
\]

The characteristic-zero degree bound `deg(F)<=320` and exact divisibility `D|F`, established separately in the previous certificate, imply `G=monic(F/D)` has degree at most 112. A C++17/GMP implementation exactly evaluated `F(R)/D(R)` at 113 distinct integer points (0..113 except 3), recovered all coefficients via *rational* Newton interpolation, and directly confirmed **three additional integer points** (114, 115, 116). This yields the exact coefficients assuming the symbolic polynomial degree bound and factor-divisibility lemmas.

Compile and regenerate (requires GMP and GMPXX development libraries):

```bash
g++ -O2 -std=c++17 -fopenmp exact_coeffs_quotient_omp.cpp -lgmpxx -lgmp -o circle_exact_generator
./circle_exact_generator
```

Output path is `/mnt/data/circle_G112_exact_coefficients.tsv`; adapt the hardcoded path if needed. It may take several minutes. OpenMP uses four threads.

## Cross-checks

1. 113-node exact interpolation, **three held-out exact characteristic-zero evaluations pass**.
2. Every one of the **113*16=1808** K-coordinate coefficients reduces modulo 10391 to the previous *independently generated* finite-field coefficients (0 discrepancies). Script: `verify_G112_exact.py`.
3. New prime **1129**, four different square-root embeddings, nine evaluation points each (36 checks) pass against the independent modular resultant evaluator; script `check_G112_new_prime.py`.
4. Using 1200-decimal-digit mpmath root approximation near `8.303468122111489078704381...`, `log10(abs(G(root)))=-1085.443046` and `log10(abs(G(root))/sum_j abs(a_j)*abs(root)^j)=-1201.571499`. This check is NUMERICAL ONLY, not a proof of the exact root relation. Script: `check_G112_root_numerically.py`.
5. A prior modular Rabin check indicated the degree-112 reduction is irreducible mod 10391; all sixteen conjugates were pairwise coprime. Given the exact polynomial produced here and good reduction, this supports irreducibility over `K` and the 1792-degree rational norm statement; those previous certificates are outside the present coefficient package.

## Remaining qualifications

- The independent existence/uniqueness proof for the real contact-closure root and algebraic elimination are documented in `circle_degree1792_proof_report.md` from the earlier turn. The monic polynomial is a **contact-configuration radius polynomial**; proving minimality of the *packing* over all configurations is a separate problem.
- The exact coefficient generator and its source were tested and modularly cross-validated but have not been formally verified in Lean/Coq or independently audited by a computer algebra package such as SageMath/Magma.
- The `G` coefficients have been expanded; the full rational norm of degree 1792 has **not** been expanded here.
