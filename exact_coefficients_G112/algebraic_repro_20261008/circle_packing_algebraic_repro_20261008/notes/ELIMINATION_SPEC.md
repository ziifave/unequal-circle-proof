# A compact algebraic eliminant for the 10-circle sqrt(i) packing candidate

**Status:** This defines an annihilating polynomial using resultants and a field norm, **not** an explicitly factored rational minimal polynomial. The candidate has not been established as the global minimum.

## Contacts and notation

Radii: `r_i = sqrt(i)`, for `i=1,...,10`.
Core circles: `2,5,6,7,8,9,10`.
Outer contacts: `2,5,6,7,8,9`.
Circle contacts: `(5,7),(2,8),(6,8),(2,9),(7,9),(5,10),(6,10),(7,10)`.

Let `X` be the unknown outer radius and `t_i=X-r_i`. Let `K=Q(sqrt(2),sqrt(3),sqrt(5),sqrt(7))`. All coefficients below belong to `K(X)`.

Define

```
c_ij(X) = 1 - 2*r_i*r_j/(t_i*t_j)
G(z; a,b) = (z-a*b)^2 - (1-a^2)*(1-b^2)
```

The polynomial for the cosine of the angular chain `7-9-2-8-6` is obtained by

```
P2(u) = G(u; c_79,c_92)
P3(v) = resultant_u(P2(u), G(v;u,c_28))
P4(w) = resultant_v(P3(v), G(w;v,c_86))
```

`P4` is a monic polynomial of degree eight in `w` (before special substitutions).

## Eliminate the rigid triangle 5-7-10

Write `a=r_5+r_10`, `b=r_7+r_10`, `d=r_5+r_7`. Define

```
lambda = (b^2+d^2-a^2)/(2*d^2)
kappa  = 4*r_5*r_7*r_10*(r_5+r_7+r_10)/d^4
c      = c_57(X)
D      = 1-c^2
q      = t_5*c - t_7
A(w)   = t_6^2+t_7^2+b^2+2*t_7*lambda*q-(r_6+r_10)^2
         -2*t_6*(t_7+lambda*q)*w
E(w)   = A(w)^2+4*t_6^2*kappa*q^2*(1-w^2)
         -D*(4*kappa*t_5^2*(t_6*w-t_7)^2
         +4*t_6^2*lambda^2*t_5^2*(1-w^2))
H(w)   = E(w)^2-16*kappa*t_6^2*(1-w^2)
         *(A(w)*q-2*D*lambda*t_5^2*(t_6*w-t_7))^2
```

The quartic `H(w)` is a necessary condition for the existence of disk 10 tangent to 5,7,6 on the branch of the given outer-circle tangencies. It comes from eliminating the two sines (of the 5-7 contact angle and the 7-to-6 angular chain) in the squared 6-10 distance constraint. Extra branches are introduced by the squaring.

## Explicit (but unexpanded) univariate annihilator

Take the numerator after clearing rational denominators:

```
P_K(X) = numerator(resultant_w(P4(w), H(w)))   in K[X]
Q(X) = primitive_part(Norm_{K/Q}(P_K(X)))     in Q[X]
```

The Packomania candidate `R0=8.303468122111489078704381187516199...` satisfies `Q(R0)=0` exactly, provided the formal resultant is calculated without an implementation error. A **minimal** polynomial must be extracted as the square-free irreducible factor of `Q(X)` having that root, followed by a rigorous isolating interval. This final factoring and isolation have **not** been carried out.

## Numeric branch used to verify the contact equations

The corresponding real branch is parameterized by

```
alpha_ij(X) = 2*asin(sqrt(r_i*r_j / (t_i*t_j)))
p7 = t7
p5 = t5*exp(+I*alpha_57)
p6 = t6*exp(-I*(alpha_79+alpha_92+alpha_28+alpha_86))
mu = sqrt(kappa)
p10= p7 + (lambda+I*mu)*(p5-p7)
F(X) = abs(p6-p10)^2-(r6+r10)^2
```

At 220-decimal-digit arithmetic, the root of `F(X)=0` has 165 displayed digits in the companion Python script; the core's contact residuals are about `1e-220`. These are numerical checks, not computer-assisted exact certificates.

Sources: E. Specht, https://www.packomania.com/ccir/ccir10.html and https://www.packomania.com/ccir/txt/ccir10.txt .
