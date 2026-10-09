# Certified global optimality: eight disks of radii 1,...,8

**Status:** Complete computer-assisted proof *as checked by the accompanying rational replay implementation*; independent mathematical/code review is still desirable. This is a research result, not a published or independently peer-reviewed theorem. Certificate discovery may use floating point, but the two replay stages use only Python integers and `fractions.Fraction` for all decisions (plus integer `isqrt` for outward square-root bounds).

## Theorem

Define for `R > i+j` the wall-wall necessary angle

\[
\beta_{ij}(R)=2\arcsin\sqrt{\frac{ij}{(R-i)(R-j)}}.
\]

Let `R0` be the unique root in `[16.22174667655772, 16.22174667655773]` of

\[
\beta_{48}(R)+\beta_{83}(R)+\beta_{36}(R)+\beta_{65}(R)+\beta_{57}(R)+\beta_{74}(R)=2\pi.
\]

Then the minimum enclosing circle radius for disjoint disks of radii `1,...,8` equals `R0`. The six disks `3,...,8` already force the lower bound, while disks 1 and 2 fit into an explicit six-disk ring witness. The older best-known numerical value `16.2217466766` coincides with the theorem's root.

## Upper bound

Construct the six wall disks in cyclic order `(4,8,3,6,5,7)`, with wall-center radial distances `R0-i`, successive angles `beta_(i,j)(R0)`, and disk 4 starting at angle zero. The critical-root equation guarantees closure, giving six tangent adjacent pairs. Set

\[
  p_1=(-3,-14),\qquad p_2=(-3,-5/2).
\]

The verifier `verify_eight_upper.py` proves strict opposite signs at the rational root interval endpoints using exact interval arithmetic for square roots, arctangents and `pi`. Since the sum of angles is strictly decreasing in `R`, it defines a unique root. It then certifies all 22 non-contact pairs and the strict containment of the two auxiliary disks. This proves `R* <= R0`.

## Lower bound: complete finite certificate

Take `U=16.22174667656>R0`. If all eight disks fit inside `R<=U`, each center radius `s_i`, for `3<=i<=8`, obeys

\[
  \ell_i=\max\!\left(0,\max_{j\ne i}(i+2j-U)\right)\le s_i\le U-i.
\]

All six `ell_i` are positive. Cyclic orders of these six labeled center rays have 60 classes up to rotation and reflection.

On any positive radial rectangle `B`, define

\[
  c_{ij}(x,y)=\frac{x^2+y^2-(i+j)^2}{2xy}.
\]

For each `q_ij` rational, the verifier checks the degree-18 rational Taylor bound

\[
  \cos(q_{ij}) \ge C_{18}(q_{ij})\ge
     \max_{x\in\{\ell_i,u_i\},y\in\{\ell_j,u_j\}}c_{ij}(x,y).
\]

The four-corner theorem applies to this `c` because its interior stationary points in either coordinate are minima, not maxima. Thus any feasible packing requires the smaller pair angle >= `q_ij`. For a lifted order `(i_0,...,i_5)`, all pairs with `a<b` satisfy

\[
  q_{i_ai_b}\le \theta_b-\theta_a\le 2\pi-q_{i_ai_b}.
\]

The checker uses the strict rational bound `pi < 3.141592653590`, itself verified by Machin's identity and alternating rational arctangent sums. Each angular leaf contains exact rational ticks and *one explicit negative directed cycle for each of the 60 relevant orders*; its total edge weight is strictly negative. No feasible packing can satisfy those necessary differences.

A binary tree of rational radial cuts exhaustively covers the initial six-dimensional radial box. The independently replayed tree has:

- **53 nodes, 26 rational splits, 27 leaves**, maximum depth 23;
- **26 leaves** with exact angular negative cycles excluding all 60 orders;
- **1 leaf** with negative cycles excluding 59 orders, leaving the single order `(8,3,6,5,7,4)`, which is a rotation of the reverse of the candidate wall ring.

### Final local barrier

At the last leaf, the lower endpoints (decimal displays only, exact rationals live in the tree) satisfy:

| Disk | Certified lower bound on `s_i` | Upper `U-i` |
|--:|--:|--:|
| 3 | 12.895387509275 | 13.221746676560 |
| 4 | 11.694028341990 | 12.221746676560 |
| 5 | 10.819028341990 | 11.221746676560 |
| 6 | 9.944028341990 | 10.221746676560 |
| 7 | 8.916310007420 | 9.221746676560 |
| 8 | 7.916310007420 | 8.221746676560 |

For each oriented adjacent pair `(i,j)` of the candidate six-cycle, the verifier proves throughout the *extended* radial intervals `[ell_i,U-i]` and `[ell_j,U-j]` the exact inequalities

\[
\ell_i+\ell_j>i+j,\qquad
\max(|\ell_i-(U-j)|, |(U-i)-\ell_j|)<i+j,
\]

\[
\boxed{\ell_i^2-(U-j)^2+(i+j)^2>0}
\]

and the same inequality with `i,j` swapped. The derivative identity

\[
  \frac{\partial\phi_{ij}(s_i,s_j)}{\partial s_i}
    =-\frac{s_i^2-s_j^2+(i+j)^2}{2s_i^2s_j\sin\phi_{ij}}
\]

therefore shows that each adjacent necessary angle strictly decreases whenever either radial coordinate is increased toward its wall location `R-i`. This is an **analytic comparison, not a physical motion**. It follows that an alleged packing with `R<R0` and the last surviving cyclic order would have

\[
  2\pi\ge \sum_{(i,j)\text{ in cycle}}\phi_{ij}(s_i,s_j)
       \ge \sum_{(i,j)\text{ in cycle}}\beta_{ij}(R)
       >\sum_{(i,j)\text{ in cycle}}\beta_{ij}(R0)=2\pi,
\]

an impossibility. Hence every radial leaf is excluded for `R<R0`. This proves `R*>=R0` and completes the theorem.

## Run

Python 3.11 or later; **standard library only**, no external packages and no `-O` or `-OO`:

```sh
python3 certify_integer_eight_global.py
```

The wrapper independently runs `verify_eight_upper.py` and `verify_eight_global_tree.py`. The discovery script `gen_eight_global_tree.py` is **not** used by the checker. The JSON certificate is `eight_global_proof_tree.json`.

Expected outcome:

```
PASS Exact root and eight-disk witness
PASS Finite rational global lower certificate
TREE {'nodes': 53, 'max_depth': 23, 'splits': 26, 'angular_leaves': 26, 'main_barrier': 1} ...
GLOBAL OPTIMALITY CERTIFIED (subject to soundness of verifier implementations)
```

An elementary corruption test also succeeds: increasing one angular tick in the JSON proof causes the independent verifier to reject the invalid inequality.

## Scope and limitations

The certificate is mathematically finite, and its verifier uses exact integer and rational proof decisions, but this is **not** an end-to-end theorem-prover formalization; it depends on the correctness of the checker, the mathematical arguments encoded by the checks, and standard Python semantics. Code review, an independent verifier, and prior-art checking should precede any priority or publication claim. The root's exact form is an isolating rational interval plus a unique monotone angular equation; an explicit minimal polynomial is **not** asserted here.
