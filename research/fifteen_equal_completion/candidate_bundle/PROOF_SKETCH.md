# Fifteen congruent unit disks in a circular container: a candidate global-optimality proof

**Status (9 October 2026).** This is a newly assembled, author-generated *candidate proof*. The automated certificates and rational inequalities reproduced locally, but the argument has **not** undergone independent mathematical scrutiny or peer review. The replay sends all 760 dihedral classes through the coarse integer angular graph and does not rely on the separate gap-capacity filter. The geometric reduction lemmas and verification code must still be checked independently before a public claim of resolution.

## Statement

Let \(R_{15}^*\) be the smallest radius of a circular container holding fifteen disjoint closed disks of radius one. The claimed formula is

\[
R_{15}^*=R_0=1+\sqrt{1+(2+\cot(\pi/5))^2}
=4.521356964706164\ldots.
\]

The argument splits into geometric lemmas, exhaustive *necessary-condition* certificates, and a local angular-barrier lemma.

## 1. Exact construction

Write \(\phi=\pi/5\), \(a_0=\csc\phi\), \(b_0=R_0-1\), \(\alpha=\phi-\arcsin(1/b_0)\). For \(k=0,1,2,3,4\), set the center of each inner disk in polar coordinates to \((a_0,2k\phi)\) and two outer centers to \((b_0,2k\phi-\alpha)\), \((b_0,2k\phi+\alpha)\).

Check all pairwise separations: adjacent inner-center separation is \(2a_0\sin\phi=2\); adjacent outer centers across cells are separated by \(2b_0\sin(\phi-\alpha)=2\); the inner-outer correspondence follows from \(a_0^2+b_0^2-2a_0b_0\cos\alpha=4\). All other center separations are larger by their angular spacing. The ten outer disks touch the container. Hence \(R_{15}^*\le R_0\).

## 2. Radius reduction and four radial populations

Put \(b_0=R_0-1\), \(L=b_0-4/b_0\), numerically \(2.38543122923\ldots\). Classify center norms \(s_i<L\) as inner (I), and \(s_i\ge L\) as outer (O). Assume a configuration is feasible at radius \(R\le R_0\); then \(s_i\le b_0\).

**Wall-pushing lemma.** Every O center may be moved radially outward to norm \(b_0\) while fixing its polar angle, without introducing overlaps. For an I–O pair with radii \(x<L\le y\), the squared distance \(x^2+y^2-2xy\cos\theta\) strictly increases with \(y\). For an O–O pair, the maximum of \(c(x,y)=(x^2+y^2-4)/(2xy)\) on \([L,b_0]^2\) is \(c(b_0,b_0)\), attained also at \((L,b_0)\) because \(L=b_0-4/b_0\). Thus the original non-overlap angular condition remains valid when both O radii are set to \(b_0\).

Let \(\theta_0=2\arcsin(1/b_0)\). Since \(11\theta_0>2\pi\), there are at most 10 O centers. Since \(L+1<R_9^*\), where the exact optimal 9-congruent-disk radius is previously established, there are at most 8 I centers. Consequently \(N_I\in\{5,6,7,8\}\). Other known small-disk optimal radii imply \(s_{(5)}\ge a_0>5/3\) and \(s_{(6)}\ge2\), yielding count constraints on the radial bins.

## 3. Exhaustive symmetry reduction and necessary angular constraints

List centers in circular polar order (arbitrary tie-breaking if necessary). Since disks are congruent, the binary I/O word of length 15 is defined modulo circular shift and reversal. There are exactly \(111,185,232,232\) dihedral classes for \(N_I=5,6,7,8\), totaling 760.

For radii \(x,y>0\), if \(x+y<2\) the pair is impossible. If \(|x-y|\ge2\) it has no angular restriction. Otherwise non-overlap implies, for increasing unwrapped angles,

\[
\arccos c(x,y)\le\theta_j-\theta_i\le 2\pi-\arccos c(x,y),\qquad i<j.
\]

For rational radius intervals, maximize \(c\) at the four corners to obtain a *safe lower bound* \(q_{ij}/2800\) on the necessary angle. For intervals starting at zero, use the separate limiting monotonicity argument; see `build_bounds3.py`, `build_bounds4.py`, `certify_six_nine.py`. The replay uses the exact rational bound \(\cos x\ge P_{18}(x)-x^{19}/19!\), proved by Taylor's theorem, and \(2\pi<44/7=17600/2800\). A negative cycle in the resulting integer difference-constraint graph implies nonexistence for the **entire radius box**. Every excluded node must have a valid geometric or graph-theoretic exclusion; no plausible numerical value is used as a proof.

The exact coarse-angle audit and 3-type integer graph test eliminate 382 classes directly, leaving 378 for refinement; no orbit is skipped by the separate gap-capacity filter. Finer 8-bin and 12-bin grids eliminate all but four classes: three I5/O10, one I6/O9. The remaining I6/O9 class has three radial boxes and is eliminated by subdividing its unique small-center interval \([0,1/2]\) into two halves (3 pair-sum contradictions and 3 negative cycles). The two noncanonical I5/O10 classes have respectively 47 and 38 coarse radius boxes; exact rational bisection closes both. Therefore any putative packing with \(R\le R_0\) must have I/O cyclic pattern **\((I,O,O)^5\)**.

For the canonical pattern, 1,181 coarse boxes are exhaustively split into 56,573 nodes. Exactly 28,846 leaves terminate by negative cycles, while 31 leaves terminate in the local box \([42/25,43/25]^5=[1.68,1.72]^5\). (The count of 56,573 includes internal nodes.) See `verify_canonical_exact.py`.

## 4. Explicit local barrier, independent of symmetry

Assume the I/O word is \((I,O,O)^5\) and all five inner radial coordinates satisfy \(a_i\in [1.68,1.72]\). Put \(b=b_0\), \(a_0=\csc(\pi/5)\), and define

\[
\Phi(x,y)=\arccos\frac{x^2+y^2-4}{2xy},\quad
h_i=\Phi(a_i,a_{i+1}),\quad
k_i=\Phi(a_i,b)+\Phi(b,b)+\Phi(a_{i+1},b),
\]

with indices mod 5. Because every \(k_i>1.175\), the four complementary inner gaps use over 4.7 radians, more than \(\pi\); thus each own inner gap is less than \(\pi\) and its direct inner-inner constraint indeed gives \(\Delta_i\ge h_i\). Traversing two outer centers gives \(\Delta_i\ge k_i\). Hence

\[
\sum_{i=1}^{5}\max(h_i,k_i)\le2\pi.
\]

At the symmetric candidate \(a_i=a_0\), \(h_i=k_i=2\pi/5\). Let \(\delta_i=a_i-a_0\), \(\sigma_i=\delta_i+\delta_{i+1}\), \(\eta=11/500=.022\). The linear coefficients are

\[
\left.\partial_x\Phi(x,y)\right|_{a_0,a_0}=-c,
\quad c=\frac{\sin^2(\pi/5)}{\cos(\pi/5)}>\frac{21}{50},
\quad d=\left.\partial_x\Phi(x,b_0)\right|_{x=a_0}>c.
\]

For \(x,y\in[1.68,1.72]\), elementary differentiation and *rational* interval comparisons verify

\[
|\partial_{xx}\Phi(x,y)|<0.3,\quad
|\partial_{xy}\Phi(x,y)|<0.8,\quad
\left|\frac{d^2}{dx^2}\Phi(x,b_0)\right|<5.
\]

The corresponding exact rational tests are in `verify_local_constants.py`. Taylor's theorem gives

\[
\begin{aligned}
h_i&\ge 2\pi/5-c\sigma_i-\tfrac52(\delta_i^2+\delta_{i+1}^2),\\
k_i&\ge 2\pi/5+d\sigma_i-\tfrac52(\delta_i^2+\delta_{i+1}^2).
\end{aligned}
\]

Since \(d>c>0\), for each real \(\sigma_i\), \(\max\{-c\sigma_i,d\sigma_i\}\ge c|\sigma_i|\). Moreover \(2\delta_i=\sigma_i-\sigma_{i+1}+\sigma_{i+2}-\sigma_{i+3}+\sigma_{i+4}\), so \(\sum|\sigma_i|\ge(2/5)\sum|\delta_i|\). Therefore

\[
\begin{aligned}
\sum_i\max(h_i,k_i)
&\ge2\pi+c\sum_i|\sigma_i|-5\sum_i\delta_i^2\\
&\ge2\pi+\left(\frac{2c}{5}-5\eta\right)\sum_i|\delta_i|\\
&>2\pi+(0.168-0.11)\sum_i|\delta_i|.
\end{aligned}
\]

If any \(\delta_i\ne0\) this contradicts the required angle sum. Thus all inner radii equal \(a_0\). Then \(\Delta_i\ge h_i=2\pi/5\) with total \(2\pi\), so all inner directions form a regular pentagon. All outer angular inequalities within each gap also saturate, forcing the ten outer centers into the previously specified contact configuration at radius \(b_0\).

Finally, if the original container had \(R<R_0\), all original outer center radii would be \(\le R-1<b_0\). Every outer disk in the forced wall-pushed layout touches at least one inner disk, and radial outward motion strictly increases the corresponding distance because each inner radius is \(a_0<L\). Therefore the original positions would overlap, contradicting feasibility. Hence \(R\ge R_0\), matching the construction.

## 5. Outstanding verification / publication caveats

* Review the wall-pushing and radial-classification proofs separately from the code.
* Review the `cmax` four-corner and zero-endpoint rules, Taylor cosine lower bound, and integrity of each radial enumeration and early-pruning rule.
* Validate the exact construction with an independent symbolic-geometry verifier (all 105 disk-disk pairs, 15 container constraints).
* Obtain an independent reimplementation or formal proof assistant replay before a public claim of resolution.
* Verify the literature and novelty claims; these scripts are *not* peer review.
