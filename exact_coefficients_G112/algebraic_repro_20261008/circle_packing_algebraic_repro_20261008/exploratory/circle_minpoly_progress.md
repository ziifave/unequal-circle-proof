# Algebraic degree investigation: 10 unequal circles with r_i=sqrt(i)

## 2026-10-08 status

Numerical candidate R0 = 8.3034681221114890787043811875161993299502137405353848095651971804960110... .
This is **not** a proof of global optimality. No characteristic-zero minimal polynomial has yet been computed.

We started from the contact graph encoded in `unequal_circles_elimination_spec.md`, then formed a polynomial in R by eliminating the angular chain variable w. Numerical evaluation of the unsquared closure and the quartic H(w) agrees at R0 to the available numerical precision.

For the split prime p=10391 and all 16 possible assignments of the four square roots mod p, the modular resultant has observed degree 320. Removing the factors

    (R + sqrt(10))^16 * product((R - sqrt(i))^32 for i in (2,5,6,7,8,9))

leaves a degree-112 polynomial in F_p[R] for every embedding.

**Verified finite-field facts:**
- In one of the 16 embeddings, the degree-112 polynomial is irreducible over F_10391. The Rabin irreducibility criterion passes: x^(p^112) = x mod f and gcd(f,x^(p^56)-x)=gcd(f,x^(p^16)-x)=1.
- Each of 16 conjugate residual polynomials has degree 112; all 120 unordered pairs have gcd 1 in F_10391[R].
- The 16 polynomials can be reconstructed as images of one degree-112 monic polynomial over (Z/pZ)[sqrt2,sqrt3,sqrt5,sqrt7], using the sign-character transform. The coefficients in the standard 16-element multiquadratic basis are saved in JSON.
- Product of the 16 residual polynomials has degree 1792 mod p. This is **not** the actual integer/rational minimal polynomial: its coefficients are only residues modulo p.

**Conditional consequence:** If the claimed extraneous factors divide the characteristic-zero resultant in K[R] exactly, leaving a degree-112 polynomial G, then G is irreducible over K by the irreducible modular reduction in one prime. The distinct conjugates imply the field norm Norm_{K/Q}(G) is irreducible over Q, of degree 16*112 = 1792. If the numeric candidate is a root of G (rather than one of the extraneous factors), this norm is its rational minimal polynomial up to scaling. The critical uncompleted step is verifying the exact quotient in characteristic zero and isolating the desired root rigorously.

`circle_exact_eliminant.sage` contains a **not-yet-executed** SageMath script intended to test exactly these statements. SageMath was unavailable in the execution environment. Running this computation may be expensive in time and memory.

## Files
- `unequal_circles_elimination_spec.md`: original contact geometry and resultant formulas.
- `circle_field_modular.py`: computes the 16 embeddings and norm mod p, with distant held-out evaluations, 120 gcd checks, and exact character inversion.
- `circle_modular_certificate.py`: independently checks irreducibility of one F_p polynomial using Rabin criterion.
- `circle_degree112_mod_10391.json`: F_p polynomials and modular 1792-degree norm, **not** a Q-coefficient minimal polynomial.
- `circle_exact_eliminant.sage`: proposed characteristic-zero computation (unexecuted).
