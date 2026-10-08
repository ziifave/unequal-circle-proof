# Global optimality completion — 2026-10-09

## Result

The global lower-bound proof is now closed for disks with radii
\(r_i=\sqrt{i}\), \(1\le i\le10\). Define \((t_{\rm crit},R_{\rm crit})\)
as the unique solution in the rational rectangle

\[
1.0037160860750841\le t\le1.0037160860750846,\qquad
8.3034681221114890\le R\le8.3034681221114900
\]

of the two exact angle equations \(A(t,R)=B(t,R)=2\pi\) specified in
[`angle_barrier_theorem_proof_2026-10-08.md`](proof/global_completion/angle_barrier/angle_barrier_theorem_proof_2026-10-08.md).
The rational boundary signs prove existence, the derivative signs prove
uniqueness in this small rectangle, and the top-edge sign proves the strict
bound

\[
8.3034681221114890\le R_{\rm crit}
<U=8.3034681221114900.
\]

An exact ten-disk configuration exists at \(R_{\rm crit}\), while every
smaller radius is excluded. Hence the optimal container radius is exactly
\(R_{\rm crit}\). This geometric definition is sufficient for the optimum;
identification with the separate high-degree algebraic root \(R_0\) is not
claimed or needed here.

## How the global cases close

The exact replay of the complete radial-tree certificate
([`certificate file`](certificates/skeleton-radial-tree-v27.json.gz)) checks
2,401 nodes, 1,200 rational splits, and 1,201 leaves covering every
configuration with container radius at most \(U\). Its original angular
ledgers closed 14,757,691 sector cases
and left 197 open:

- 193 cases have seven-disk core order \((10,5,7,9,2,8,6)\). Their complete
  disk-10 radial intervals lie in \([0.8588,1.1265]\). The attached radial
  angle-barrier theorem applies to all 193 without moving disks or assuming a
  wall-push condition.
- Four cases have masks \((5,16,40,2)\) (three cases) or \((4,16,41,2)\) (one
  case). Their order after deleting disk 1 is
  \((10,3,7,5,8,4,6,9,2)\), covered by the exact nine-circle negative-cycle
  certificate. The verifier also replays the second possible 4/6 order.

The radial tree had also closed 145 core-order models and two full-order witnesses
using its local terminal rule. The completion checker reclassifies each of
those 147 terminals through the same seven-disk angle-barrier theorem: every
one has the required core order and disk-10 interval. Thus these closures no
longer depend on the separate local-optimality premise.

The angle-barrier derivative check covers the radius interval required by
the global cases. Every main-core case and each of the 147
reclassified local terminals has \(t=s_{10}\le1.1265\). Non-overlap of disks
9 and 10 gives \(s_9+t\ge3+\sqrt{10}\), while containment of disk 9 gives
\(R\ge3+s_9\). Since \(\sqrt{10}>3.1\), every such feasible case satisfies
\[
R\ge6+\sqrt{10}-t
>6+3.1-1.1265
=7.9735.
\]
Thus every angle-barrier application lies in the interval on which its
derivative signs are certified. The alternative nine-circle theorem covers
its four cases for all \(R\le U_+=8.30346812212\), and the other tree leaves
are closed by their exact cycle or radial contradictions. Since
\(R_{\rm crit}<U\), all configurations with \(R<R_{\rm crit}\) are covered.
The root's exact ten-disk construction supplies the matching upper bound.

The composition checker expands every residual sector mask into all
sector-compatible orders before connecting it to a geometric theorem. It
checks 790 projected orders: 772 have the main seven-circle restriction and
18 reduce to one of the two nine-circle orders. The 147 reclassified local
terminal models are each checked separately.

## Reproduction

Run the complete proof composition with the locked workspace environment:

    uv run --locked python tools/verify_global_optimality_completion.py

The checker writes
[the JSON composition report](artifacts/global-optimality-completion-2026-10-09.json),
including SHA-256 hashes for the tree, theorem certificates, verifier
sources, locked Python environment, root README, and manuscript source and
PDF. The case tree, report, paper, and input manifest are kept together in the release commit. The
checker refuses Python's optimized `-O`/`-OO` modes so component assertions
cannot be disabled accidentally.
The individual attached theorem verifiers and certificates are preserved in
[proof/global_completion](proof/global_completion).

## Scope and trust

All proof decisions in the composition, root, and nine-circle verifiers use
exact rational/integer arithmetic. Floating-point routines may help discover
candidate bounds, but every accepted certificate inequality is checked
exactly. The radial tree and its split endpoints are also replayed exactly. The
result is a reproducible computational proof, not a Lean formalization. It
proves equality to the angle-defined exact \(R_{\rm crit}\), not equality to
the previously computed polynomial root \(R_0\).
