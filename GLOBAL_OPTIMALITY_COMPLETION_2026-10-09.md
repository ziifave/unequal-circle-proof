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

The exact replay of [`skeleton-radial-tree-v27.json.gz`](certificates/skeleton-radial-tree-v27.json.gz)
checks 2,401 nodes, 1,200 rational splits, and 1,201 leaves covering every configuration with container radius
at most \(U\). Its original angular ledgers closed 14,757,691 sector cases
and left 197 open:

- 193 cases have seven-disk core order \((10,5,7,9,2,8,6)\). Their complete
  disk-10 radial intervals lie in \([0.8588,1.1265]\). The attached radial
  angle-barrier theorem applies to all 193 without moving disks or assuming a
  wall-push condition.
- Four cases have masks \((5,16,40,2)\) (three cases) or \((4,16,41,2)\) (one
  case). Their order after deleting disk 1 is
  \((10,3,7,5,8,4,6,9,2)\), covered by the exact nine-circle negative-cycle
  certificate. The verifier also replays the second possible 4/6 order.

The v27 tree had also closed 145 core-order models and two full-order witnesses
using its local terminal rule. The completion checker reclassifies each of
those 147 terminals through the same seven-disk angle-barrier theorem: every
one has the required core order and disk-10 interval. Thus these closures no
longer depend on the separate local-optimality premise.

The angle-barrier theorem needs \(R\ge7.9\). The 7.9 lower-bound certificate
has therefore been replayed separately with a new exact-rational verifier.
It checks all 46,080 radial/order cells using integers and `Fraction`; it does
not require MPFI or any floating-point inequality decision. The existing MPFI
kernel could not be built in this environment because its development headers
are absent, so this independent replay removes that dependency.

The new refined root rectangle lies strictly below the v27 cap \(U\), so every
putative packing with \(7.9\le R<R_{\rm crit}\) is inside the tree's certified
radial domain. Combining the 193 angle-barrier cases, the four nine-circle
cases, all 147 reclassified local terminals, and the tree's exact cycle and
radial contradictions leaves no open sector case. The root's exact ten-disk
construction supplies the matching upper bound.

## Reproduction

Run the complete proof composition with the locked workspace environment:

```bash
uv run --locked --no-sync python tools/verify_global_optimality_completion.py
```

The checker writes
[`artifacts/global-optimality-completion-2026-10-09.json`](artifacts/global-optimality-completion-2026-10-09.json),
including SHA-256 hashes for the tree, certificates, and verifier sources.
The independent 7.9 replay can also be run alone:

```bash
uv run --locked --no-sync python tools/verify_fixed_order_rational_certificate.py
```

The individual attached theorem verifiers and certificates are preserved in
[`proof/global_completion`](proof/global_completion).

## Scope and trust

All proof decisions in the new composition, root, nine-circle, and 7.9
verifiers use exact rational/integer arithmetic. `math.acos` in the 7.9
verifier only proposes a rational angle tick; an exact cosine Taylor inequality
must pass before that tick is used. The v27 tree and its split endpoints are
also replayed exactly. The result is a reproducible computational proof, not a
Lean formalization. It proves equality to the angle-defined exact \(R_{\rm
crit}\), not equality to the previously computed polynomial root \(R_0\).
