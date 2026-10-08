# A computer-assisted exact degree certificate for the sqrt(i) ten-circle packing candidate

**Date:** 2026-10-08  
**Scope:** Algebraic degree of the *candidate configuration's* containing radius. **NOT** a certificate that this is the global packing optimum.

## Statement

Let `r_i = sqrt(i)` for `i=1,...,10`. In the contact pattern specified in `unequal_circles_elimination_spec.md`, define its real closure-equation root `rho` by the unique root in

```
8.3034681221114890787043811875161993
< rho <
8.3034681221114890787043811875161994.
```

Under the contact-geometry identities given below (and verified against the original closure equation), the degree of `rho` over Q is **1792**. An exact unexpanded minimal polynomial is provided via resultants and a field norm; its coefficients in Z have **not** been expanded.

## Exact field and eliminant

Set `K = Q(sqrt(2),sqrt(3),sqrt(5),sqrt(7))`, a degree-16 multiquadratic field. Note `sqrt(6),sqrt(8),sqrt(10)` lie in K, while `sqrt(9)=3`.

For each pair of outer-circle-tangent disks, put

```
t_i = R-r_i
D_ij = t_i*t_j
N_ij = D_ij-2*r_i*r_j
c_ij = N_ij/D_ij
G(z;a,b) = (z-a*b)^2-(1-a^2)*(1-b^2).
```

Let `A_ij(v,u) = D_ij^2*G(v;u,c_ij)`, a polynomial in `K[R,v,u]` (denominators cancel). Define the angular-chain polynomials

```
P2(u) = D_79^2*D_92^2*G(u; c_79,c_92),
P3(v) = Res_u(P2(u), A_28(v,u)),
P4(w) = Res_v(P3(v), A_86(w,v)).
```

These have degrees 2, 4, and 8 in their angular variables. Define a quartic `H(w)` by

```
a = r_5+r_10; b = r_7+r_10; d = r_5+r_7
lambda=(b^2+d^2-a^2)/(2*d^2)
kappa=4*r_5*r_7*r_10*(r_5+r_7+r_10)/d^4
q=t_5*N_57-t_7*D_57
J=D_57^2-N_57^2
A(w)=(t_6^2+t_7^2+b^2-(r_6+r_10)^2)*D_57
     -2*t_6*t_7*D_57*w+2*lambda*q*(t_7-t_6*w)
E(w)=A(w)^2+4*t_6^2*kappa*q^2*(1-w^2)
     -J*(4*kappa*t_5^2*(t_6*w-t_7)^2
         +4*t_6^2*lambda^2*t_5^2*(1-w^2))
T(w)=A(w)*q-2*J*lambda*t_5^2*(t_6*w-t_7)
H(w)=E(w)^2-16*kappa*t_6^2*(1-w^2)*T(w)^2.
```

Then `F(R)=Res_w(P4(w),H(w))` is a polynomial in `K[R]`.

## Lemma 1: characteristic-zero extraneous factors

For a linear factor `delta=R-r_i`, the following **lower bounds** on the valuations of the coefficients of the two angular polynomials hold (where `j` means the coefficient of `w^j`):

| delta | P4 | H | Guaranteed multiplicity of delta in F |
|---|---|---|---:|
| `R-r_2` | all coefficients divisible by delta^8 | -- | 32 |
| `R-r_5` | -- | all coefficients divisible by delta^4 | 32 |
| `R-r_6` | `[w^j]P4` divisible by delta^j | `[w^j]H` divisible by delta^j | 32 |
| `R-r_7` | `[w^j]P4` divisible by delta^j | `[w^j]H` divisible by delta^j | 32 |
| `R-r_8` | all coefficients divisible by delta^8 | -- | 32 |
| `R-r_9` | all coefficients divisible by delta^8 | -- | 32 |
| `R+r_10` | -- | all coefficients divisible by delta^2 | 16 |

The bounds on `P4` follow from valuation propagation through the Sylvester determinants used to define `P2,P3,P4` (`circle_content_lower_bounds.py`). The bounds on `H` at `r_5,r_6,r_7,-r_10` were checked by **exact rational arithmetic in the 16-dimensional multiquadratic basis**, expanding `H` in the local parameter `delta` up to degree 4 (`circle_local_field.py`). No floating point operations or reduction modulo a prime are used for these computations.

For the first/second kind of content factor, use homogeneity of the resultant in the coefficients: `Res(P4,delta^e H)=delta^(8e) Res(P4,H)` and `Res(delta^e P4,H)=delta^(4e) Res(P4,H)`. For `r_6` and `r_7`, both polynomials have the form `P4(w)=P4_tilde(delta*w)` and `H(w)=H_tilde(delta*w)`. Hence `Res_w(P4,H)=delta^(8*4)Res(P4_tilde,H_tilde)`.

Thus, **in characteristic zero**, the exact polynomial

```
Dextr(R) = (R+sqrt(10))^16 * product((R-sqrt(i))^32
                                        for i in [2,5,6,7,8,9])
```

divides `F(R)` in `K[R]`. Its degree is `16+6*32=208`.

## Lemma 2: characteristic-zero degree bound 320

Set `t=1/R` and `w=1-t^2*z`. Because

```
c_ij = 1-t^2 * (2*r_i*r_j)/((1-r_i*t)*(1-r_j*t)),
```

an angular-polynomial addition step `A_ij(v,u)` becomes a polynomial (regular at `t=0`) upon substituting `v=1-t^2*z` and `u=1-t^2*zu`. The starting 2-contact equation satisfies

```
t^4 P2(1/t,1-t^2*z) in K[t,z].
```

Resultant covariance under `u=1-t^2*zu` successively gives

```
t^16 P3(1/t,1-t^2*z) in K[t,z],
t^48 P4(1/t,1-t^2*z) in K[t,z].
```

In `H`, note `q=(r_7-r_5)*D_57-2*r_5*r_7*t_5`, `J=4*r_5*r_7*(D_57-r_5*r_7)`, and `t_6*w-t_7 = (r_7-r_6)-t*z+O(t^2)`. The grouped formula for `H` then proves

```
t^8 H(1/t,1-t^2*z) in K[t,z].
```

Using the formula `Res_z(f(1-t^2*z),g(1-t^2*z))=t^(2*deg(f)*deg(g))*Res_w(f,g)` and homogeneity with degrees 8 and 4, we obtain

```
t^320 F(1/t) in K[t].
```

Hence `deg_R F <= 320`. For the finite-field reduction `p=10391` and `sqrt(2,3,5,7)=(1360,2293,4804,4529)`, the leading coefficient at this bound is `5395 != 0` (`circle_degree_leading_mod.py`), showing **deg F = 320** in characteristic zero.

Combining with Lemma 1, `G(R):=F(R)/Dextr(R)` belongs to `K[R]` with **degree exactly 112**.

## Lemma 3: irreducibility over K and Q

Reduce the **characteristic-zero polynomial G** modulo the split prime 10391 through the ring map `sqrt(2,3,5,7) -> (1360,2293,4804,4529)`. Because `deg G <=112`, 113 exact finite-field evaluations uniquely reconstruct its reduction, and 12 + 4 held-out points confirm the evaluation/interpolation identity (`circle_field_modular.py`; all arithmetic in finite fields). The normalized 112-degree polynomial passes Rabin's irreducibility criterion:

```
x^(p^112) = x (mod f),
gcd(f, x^(p^56)-x) = 1,
gcd(f, x^(p^16)-x) = 1.
```

These checks are repeated independently in `circle_modular_certificate.py`. Consequently, `G` is irreducible over K (using the standard good-reduction irreducibility lemma).

Under the 16 sign embeddings of K, the 16 corresponding degree-112 reductions are **pairwise coprime in all 120 pairs**. Therefore the exact conjugates of `G` over K are distinct, and the norm of the monic `G` is irreducible over Q:

```
P_Q(R) := Norm_{K/Q}( G(R)/leading_coefficient(G) ).
```

This is a **monic degree-1792 polynomial in Q[R]**; multiplying by a common denominator and taking primitive part gives the corresponding primitive integer minimal polynomial.

## Lemma 4: the desired real packing radius is a root

The original unsquared geometric closure equation, with principal positive sines and a fixed orientation of the rigid `(5,7,10)` triangle, has a **unique** root in the displayed rational interval: exact outward-rounded rational interval arithmetic finds a strict sign change and `f'(R)>29.7522` everywhere in the interval (`circle_radius_root_interval_certificate.py`).

On this real branch, let `w` be the cosine of the sum of the four outer tangency angles from 7 to 6. Angle addition forces `P4(R,w)=0`; eliminating the positive square roots in the rigid-triangle closure forces `H(R,w)=0`. Thus `F(rho)=0` exactly. Since `rho>8` and is not any of `sqrt(2),sqrt(5),sqrt(6),sqrt(7),sqrt(8),3,-sqrt(10)`, `Dextr(rho)!=0`, so **G(rho)=0**. Thus `P_Q(rho)=0`.

Combining Lemmas 1–4 yields `degree_Q(rho)=1792`.

## Audit status and limitations

- The factor-divisibility and degree-bound arguments are **characteristic-zero**, not extrapolations from characteristic p alone.
- The arithmetic outputs (rational field / finite field / rational intervals) are exact and reproducible, but the full proof has **not** been formalized in Lean/Coq and has not been independently checked by a second CAS. Audit of the geometric-elimination identities and Python implementations is recommended before publication.
- Neither a 1793-term expanded polynomial nor an explicitly primitive integer coefficient list has been produced.
- This is **not** a proof that the 10-circle packing is globally optimal: it identifies the algebraic degree of one rigorously isolated contact-configuration radius only.

## Files

- `unequal_circles_elimination_spec.md` — original geometry.
- `circle_content_lower_bounds.py` — tropical lower bounds for the coefficients of P4.
- `circle_local_field.py` — exact multiquadratic characteristic-zero Taylor checks for H.
- `circle_degree_leading_mod.py` — independent coefficient-of-R^320 test modulo p.
- `circle_field_modular.py`, `modular_eliminant.py` — finite-field interpolation of the degree-112 quotient and its 16 conjugates.
- `circle_modular_certificate.py` — independent Rabin irreducibility test.
- `circle_radius_root_interval_certificate.py` — rational interval certificate for rho.
- `circle_degree112_mod_10391.json` — modular coefficient tables (not characteristic-zero coefficients).
