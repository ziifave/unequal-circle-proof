# Seven-disk angle-barrier theorem — independent rigorous proof

Date: 2026-10-08. This is a standalone *conditional geometric lower-bound theorem* with a new exact existence and ten-disk upper-bound witness. It is **not** a certificate that the v27 tree is fully closed, nor a proof that the critical radius below is identical to an independently specified degree-1792 algebraic root.

## Definitions

Let `r_i = sqrt(i)` for `i=1,...,10`. For `R>0`, let the seven labeled disks `K={2,5,6,7,8,9,10}` be packed without overlapping in a container disk of radius `R` centered at the origin. Their center distances to the origin are `s_i`. Assume that their directions have cyclic order

`(10,5,7,9,2,8,6)`.

Put `W={2,5,6,7,8,9}`, `t=s_10`, and `I=[8588/10000,11265/10000]`. For `i in {5,6,7}` and for each consecutive wall pair `(i,j)` among `(5,7),(7,9),(9,2),(2,8),(8,6)`, set

```
a_i(R) = R-r_i
D_i = r_10+r_i
alpha_i(t,R) = acos((t^2+a_i(R)^2-D_i^2)/(2*t*a_i(R)))
beta_ij(R) = 2*asin(sqrt(r_i*r_j/(a_i(R)*a_j(R))))
C(R) = beta_79(R)+beta_92(R)+beta_28(R)+beta_86(R)
A(t,R) = alpha_5(t,R)+beta_57(R)+C(R)+alpha_6(t,R)
B(t,R) = alpha_7(t,R)+C(R)+alpha_6(t,R)
```

These are special cases of the general angle phi_ij(x,y) defined by
cos(phi_ij)=(x^2+y^2-(r_i+r_j)^2)/(2*x*y):
alpha_i=phi_10,i(t,a_i) and beta_ij=phi_ij(a_i,a_j).
The critical pair is characterized geometrically by
alpha_5+beta_57=alpha_7 (the two contact routes from disk 10 to disk 7)
and alpha_7+C+alpha_6=2*pi (cycle closure). Equivalently, these are
F=A-B=0 and G=B-2*pi=0.

All quantities used below have real arguments on the indicated compact intervals; this is checked by the rational-only verifier.

Define the exact rational rectangle

```
J_R = [8.30346812210,8.30346812212]
J_t = [1.00371608606,1.00371608609]
```

and let `R_crit,t_crit` be the unique solution in this rectangle of `A=B=2*pi`, whose existence and uniqueness are proved below. This *defines* `R_crit` independently of any algebraic norm polynomial.

## Lemma 1: Pushing to the same container wall

Suppose `R<=U`, a feasible packing has `s_i>=L_i>0` and `s_j<=V_j` for all `j != i`, and

`L_i^2 - V_j^2 + (r_i+r_j)^2 >= 0` for all `j` in the seven-disk core other than `i`.

Moving disk `i` outward along its fixed ray by any `0 <= h <= R-r_i-s_i` preserves feasibility of every pair with `i` and preserves container inclusion. Indeed nonoverlap implies

`2*s_j*cos(theta_ij) <= (s_i^2+s_j^2-(r_i+r_j)^2)/s_i`.

Consequently the change of squared pair distance is

```
Delta_ij = h*(2*s_i+h-2*s_j*cos(theta_ij))
         >= h*((s_i^2-s_j^2+(r_i+r_j)^2)/s_i+h)
         >= h^2 >= 0.
```

Push the six disks of `W` successively. After earlier moves the other radial bounds `s_j<=U-r_j` still hold. Thus if all pairwise sufficient conditions are verified by a case box, the six disks may be put on the wall **of the original radius R** without changing t, cyclic order, or feasibility of this core.

## Lemma 2: Two necessary angular inequalities

After this push, each `i in W` has radius `a_i=R-r_i`. For a wall-wall pair `ij`, the smallest possible central angle is `beta_ij`, by the law of cosines: `1-cos(beta_ij)=2*r_i*r_j/(a_i*a_j)`. For disk 10 and wall disk `i`, the smallest possible central angle is `alpha_i`, also by the law of cosines. The angle for the *directed* consecutive arc in the cyclic order is at least the smaller angle, even if the directed gap exceeds pi.

The directed arcs of the loop `10->5->7->9->2->8->6->10` sum to `2*pi`. Bounding each arc below by its `alpha` or `beta` gives `A(t,R)<=2*pi`.

For `B`, use the loop `10->7->9->2->8->6->10`. Disk 5 is *skipped in the angle accounting* but not removed from the packing. The direct arc `10->7` is at least the smaller central angle for disks 10 and 7, `alpha_7`. Thus `B(t,R)<=2*pi`.

## Lemma 3: Rigorous signs and derivatives

At any `R in J_R`, define for `i in {5,6,7}`

```
a_i = R-r_i,
D_i = r_10+r_i,
b_i = a_i^2-D_i^2,
z=t^2,
H_i = 4*a_i^2*z-(z+b_i)^2.
b_i = (a_i-D_i)*(a_i+D_i) = (R+r_10)*(R-r_10-2*r_i)
H_i = ((a_i+D_i)^2-t^2)*(t^2-(a_i-D_i)^2)
```

On the geometric domain `0<t<a_i+D_i`, the condition
`H_i>0` is equivalent to the strict triangle inequalities
`|a_i-D_i|<t<a_i+D_i`. Where these angles are defined, direct
differentiation gives

`partial_t alpha_i=(b_i-z)/(t*sqrt(H_i))`.

On all `t in I`, exact rational interval arithmetic certifies

```
b_5-z > 0, b_6-z > 0, z-b_7 > 0.
```

Thus `A_t=alpha_5,t+alpha_6,t>0`, while `alpha_7,t<0`. In order to prove `B_t=alpha_7,t+alpha_6,t<0`, square the positive terms and check

```
(z-b_7)^2*H_6-(b_6-z)^2*H_7 = 4*z*Q(z),
Q(z) = D_6^2*(z-b_7)^2-D_7^2*(z-b_6)^2.
```

The factorization follows by expansion using `b_i=a_i^2-D_i^2`. Put
`X=D_6(z-b_7)` and `Y=D_7(b_6-z)`, both positive on the interval.
Then `Q=(X-Y)(X+Y)`, and `X>Y` is equivalent to
`z>(D_6b_7+D_7b_6)/(D_6+D_7)`.
The exact rational interval checker proves `D_6>5.6`, `D_7<5.9`,
`b_7<-1.6`, `2.75<b_6<2.8`, and `z>0.73`. Hence
`X>5.6(0.73+1.6)=13.048`, whereas
`Y<5.9(2.8-0.73)=12.213`. Therefore `Q>0` and `B_t<0`.

At fixed `t`, using `a_i=R-r_i`, another exact differentiation gives

```
partial_R alpha_i=-(a_i^2+D_i^2-t^2)/(a_i*sqrt(H_i)) <0,
partial_R beta_ij=-(1/a_i+1/a_j)*sqrt(r_i*r_j/(a_i*a_j-r_i*r_j)) <0.
```

Equivalently, partial_R beta_ij=-(1/a_i+1/a_j)*tan(beta_ij/2).
The interval checker verifies a_i^2+D_i^2-t^2>0, the strict triangle
conditions, and a_i*a_j-r_i*r_j>0. Thus each radial derivative is negative
separately, and A_R<0 and B_R<0 follow term by term.

All domains and displayed signs hold for `t in I`, `R in [7.9,8.30346812212]`, while the derivative-in-t comparison above holds for `R in J_R`. All sign endpoints are checked using only exact fractions and integer square root in the attached script.

## Theorem 1: Critical exact root exists and is unique in the rectangle

Let

```
F(t,R)=A(t,R)-B(t,R)=alpha_5+beta_57-alpha_7,
G(t,R)=B(t,R)-2*pi.
```

The rational-only checker verifies the following strict inequalities **for every coordinate on each indicated rectangle edge**:

```
F(t_low, R) < 0    for R in J_R,
F(t_high,R) > 0    for R in J_R,
G(t,R_low)  > 0    for t in J_t,
G(t,R_high) < 0    for t in J_t.
```

The angle evaluations use `alpha=4*atan(tan(alpha/4))`, the analogous identity for beta, Machin's exact arctangent identity for pi, and alternating Taylor enclosures for the arctangent on `[0,1/2)`. Uncertainties from varying the other coordinate along an edge are bounded using verified interval enclosures for `partial_R F` and `partial_t G` and the mean-value theorem; no numerical tolerance is used for a proof decision.

Because `F_t=alpha_5,t-alpha_7,t>0` throughout the rectangle, each `R in J_R` has exactly one `t(R) in J_t` with `F(t(R),R)=0`. The function `t(R)` is continuous. The checked opposite signs for `G(t(R_low),R_low)` and `G(t(R_high),R_high)` imply by the intermediate value theorem that some `R_crit in J_R` satisfies `G(t(R_crit),R_crit)=0`. Put `t_crit=t(R_crit)`.

This pair is unique in `J_t x J_R`. If two solutions have `R_1<R_2`, then at `(t_1,R_2)` both `A` and `B` are strictly below `2*pi` (as both decrease in R). To regain `A=2*pi` by changing t requires **increasing** t, while to regain `B=2*pi` requires **decreasing** t, impossible. At fixed R, strict monotonicity of A in t gives uniqueness.

## Theorem 2: The angular barrier (the lower bound actually used in the global tree)

Assume `7.9<=R<R_crit`, `t in I`, the specified cyclic order, and that the six wall-push sufficient conditions of Lemma 1 have been checked in the original radial box. After pushing, Lemma 2 requires `A(t,R)<=2*pi` and `B(t,R)<=2*pi`.

If `t>=t_crit`, then

`A(t,R) > A(t,R_crit) >= A(t_crit,R_crit)=2*pi`, contradiction.

If `t<=t_crit`, then

`B(t,R) > B(t,R_crit) >= B(t_crit,R_crit)=2*pi`, contradiction.

As every real t is in one of these two cases, no such packing of the core exists for `R<R_crit`. **Therefore any feasible full ten-disk packing belonging to such a radial box satisfies `R>=R_crit`.** (A global theorem still requires every remaining radial box and other cyclic order to be covered.)

## Theorem 3: An actual ten-disk configuration at exactly R_crit

For the exact pair `t_crit,R_crit`, place the seven core centers at radial distances `t_crit` for disk 10 and `R_crit-r_i` for the other six, with cumulative polar directions

```
10: 0
5:  alpha_5
7:  alpha_5+beta_57 (=alpha_7)
9:  alpha_5+beta_57+beta_79
2:  previous+beta_92
8:  previous+beta_28
6:  previous+beta_86 (=2*pi-alpha_6)
```

The equations `F=0` and `G=0` ensure the eight exact contacts `(10,5),(10,7),(10,6),(5,7),(7,9),(9,2),(2,8),(8,6)` by the law of cosines and angular closure. The verifier checks that all other 13 core pairs are strictly separated, uniformly for all parameters in `J_t x J_R`.

Place the remaining three centers at these **fixed rational coordinates**:

```
p_1 = (-3.9798,  6.1148)
p_3 = ( 6.4777,  0.8849)
p_4 = ( 5.5222, -2.7574)
```

The same verifier checks all 37 non-contact pairs among all ten disks, as well as strict container inclusion of circles 1,3,4 and circle 10, uniformly for the rational root rectangle. As diagnostics, the smallest lower bound for `distance_squared-(r_i+r_j)^2` among those 37 pairs is >0.05489, and the smallest lower bound for `(R-r_i)^2-|p_i|^2` among the three rational-center disks is >0.11105. Hence a **ten-disk packing at the exact R_crit exists**; not merely a numerical picture.

## What is and is not concluded

1. Established: an exact `R_crit` in `J_R` exists uniquely; all derivative signs needed for the angular barrier hold; the sufficient wall-push lemma holds; there is an actual ten-disk packing at `R_crit`.
2. Established conditionally on each box: if the wall-push inequalities and the target order / t interval hold, that box admits no packing of radius `R<R_crit`.
3. Not yet established here: v27's 159 claimed applications have been rechecked against their raw box data; the other 38 cases are closed; the earlier certified algebraic radius `R_0` is exactly this `R_crit`. Numerical overlap of intervals alone is not an equality proof.
4. To finish the original project, integrate this barrier as a checker-recognized lower-bound leaf, replay every applicability condition from the original v27 certificate, close the other leaves, and prove algebraic-root identity if that specific algebraic characterization is required. The **geometrically defined exact R_crit already suffices as a legitimate proposed optimal radius** for a fully self-contained geometric result once all lower-bound cases close.

## Reproduction

Run `python certified_angle_root.py` using the bundled standalone checker. It uses `fractions.Fraction` and `math.isqrt`, no floating-point quantities in any inequality test. Diagnostic formatting converts exact rationals to decimal strings for display only. Sign checks include:

- all four signed rectangle edges (existence), and the derivative bounds used to validate the whole edges rather than individual sampled points;
- all 13 non-contact core pair distances;
- signs for `A_t>0, B_t<0, A_R<0, B_R<0`;
- 37 non-contact pairs and exact-rational placements for circles 1,3,4.
