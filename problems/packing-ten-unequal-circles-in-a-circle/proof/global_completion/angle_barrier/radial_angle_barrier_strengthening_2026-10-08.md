# Stronger angular barrier without moving any disk

2026-10-08. Proof for all radial arrangements of the seven-disk core
`K={2,5,6,7,8,9,10}` with cyclic order `(10,5,7,9,2,8,6)` and
disk-10 radius `t` in `I=[0.8588,1.1265]`.

**Scope:** This is a theorem about all arrangements in the specified **cyclic order**. It does not handle the other 4 residual v27 cases with large-circle skeleton `(10,7,8,9)`. It also does not replay v27, whose raw JSON and source files are not present among the provided attachments. Thus it is not a complete global-optimality certificate.

## Statement

Let `r_i=sqrt(i)` for `1<=i<=10`. Let

- `U=8.303468122111490`,
- `7.9<=R<R_crit`, with the exact `R_crit` defined by the unique angle root in the attached `certified_angle_root.py`,
- `t=|p_10|` in `[0.8588,1.1265]`,
- all seven disks of `K` lie inside the radius-`R` container without overlap, and their center directions occur in order `(10,5,7,9,2,8,6)`.

Then **no such seven-disk packing exists**. In particular, any ten-disk packing obeying these order and `t` hypotheses must satisfy `R>=R_crit`.

Unlike the earlier angle-barrier theorem, NO wall-push inequalities are assumed, and no disk is physically moved.

## Proof

For center distances `s_i,s_j>0`, the *necessary small angle* is

`phi_ij(s_i,s_j)=acos((s_i^2+s_j^2-(r_i+r_j)^2)/(2*s_i*s_j))`,

provided `|s_i-s_j| < r_i+r_j <= s_i+s_j`.

For any feasible arrangement, the actual directed angular gaps of the cyclic paths

`10->5->7->9->2->8->6->10` and `10->7->9->2->8->6->10`

are at least the corresponding `phi_ij`, so the sums of necessary angles, denoted
`A_radial` and `B_radial`, are both `<=2*pi`. These are identical to `A(t,R)` and
`B(t,R)` in the root theorem if all six non-10 radial coordinates are replaced
by their wall values `R-r_i`.

### Step 1. Independent radial enclosures

The containment inequality and non-overlap with disk 10 show that, for every
`i in W={2,5,6,7,8,9}`,

`L_i = sqrt(10)+sqrt(i)-1.1265 <= s_i <= U-sqrt(i) = V_i`.

Indeed `r_i+r_10 <= |p_i-p_10| <= s_i+t <= s_i+1.1265`.

These intervals can be widened outward to rational endpoints by taking floor-
scaled integer square roots. They are not assumptions about v27's radial boxes.

### Step 2. Angular derivatives

Put `d_ij=r_i+r_j` and `X_ij=s_i^2-s_j^2+d_ij^2`. Wherever the angle is in `(0,pi)`, differentiation gives

`d(phi_ij)/d(s_i) = -X_ij/(2*s_i^2*s_j*sin(phi_ij))`.

Thus the sign is negative whenever `X_ij>0`. Exact rational endpoint bounds prove `X_ij>0` everywhere in the radial box for all the individual derivatives involving pairs

`(5,10),(5,7),(7,5),(7,9),(7,10),(6,8),(6,10)`.

For the only three outer variables whose two neighboring contributions can
have different signs, we need the following stronger combined inequalities:

- `i=9` with positive contribution to `-derivative` from `(9,7)` and possibly adverse `(9,2)`;
- `i=8` with positive contribution from `(8,6)` and possibly adverse `(8,2)`;
- `i=2` with positive contribution from `(2,9)` and possibly adverse `(2,8)`.

### Step 3. The only difficult neighbor angles

For `ij in {(9,2),(2,8)}`, the certified radial rectangles satisfy

`0 <= cos(phi_ij) <= 4/5`.

Proof of the upper bound: the inequality is equivalent to

`s_i^2+s_j^2-(8/5)*s_i*s_j <= d_ij^2`.

The left side is jointly convex (positive definite quadratic form). Its maximum on a rectangle occurs at one of four corners. All four rational corner inequalities are strictly satisfied for both pairs. Their smallest **positive safety gaps** (right minus left) are greater than

- `2.172803` for `(9,2)`;
- `0.494875` for `(2,8)`.

The lower bound `cos(phi_ij)>0` follows from `L_i^2+L_j^2>d_ij^2`, also certified with rational sqrt upper bounds. Therefore

`sin(phi_92), sin(phi_28) >= 3/5` throughout the radial rectangle.

### Step 4. The three combined derivative inequalities

For each `(i,g,b)` equal to `(9,7,2)`, `(8,6,2)`, `(2,9,8)`, the derivative of the two adjacent necessary angles with respect to `s_i` has the sign of

`- X_ig/(s_g*sin(phi_ig)) - X_ib/(s_b*sin(phi_ib))`.

Here `X_ig>0`; the second numerator may be negative. Using the rational radial enclosures and the sine lower bound from Step 3,

`X_ig/(s_g sin(phi_ig)) + X_ib/(s_b sin(phi_ib))`

is bounded below by

`(L_i^2 - V_g^2 + d_ig^2)/V_g`
` - max(0, V_b^2-L_i^2-d_ib^2)/((3/5)*L_b)`.

Exact rational tests in the attached independent verifier show the following positive lower bounds:

| radial coordinate | lower bound for combined sign expression |
|---|---:|
| `s_9` | > 3.193809 |
| `s_8` | > 0.143756 |
| `s_2` | > 0.589640 |

Consequently, for both `A_radial` and `B_radial`, each coordinatewise partial derivative with respect to `s_i`, for `i in W`, is strictly negative where the angles are interior. For any corner cases with angle equal to `pi`, the result follows by continuity.

### Step 5. The wall-angle inequalities without wall-pushing

Starting with the original feasible **radii only**, replace each `s_i` by
`R-r_i` one at a time **inside the angle formulas**. This is not a physical
movement of the disks, so no concern about transient overlaps with
nonconsecutive disks arises.

For adjacent pairs in the two path formulas, the sum of their radial
coordinates can only increase during these substitutions, while the exact rational
checker shows `|s_i-s_j|<d_ij` over the whole radial box (with fixed
`t` for disk 10). Therefore the angle formulas remain real and continuous
throughout these substitutions. All coordinatewise angular sums are
non-increasing, so

`A_radial >= A(t,R)` and `B_radial >= B(t,R)`.

Since the original feasible packing requires `A_radial<=2*pi` and
`B_radial<=2*pi`, we have **both wall-angle necessary inequalities** without ever using the old wall-push lemma.

### Step 6. Finish with the certified root and opposite monotonicities

The separate certified root theorem supplies the exact unique pair
`(t_crit,R_crit)` with `A=B=2*pi`, proves `A_t>0`, `B_t<0` at `R_crit` for `t in I`, and proves both `A_R<0` and `B_R<0` for `7.9<=R<=R_crit`, `t in I`.

If `t>=t_crit`, then `A(t,R)>2*pi`, while if `t<=t_crit`, then
`B(t,R)>2*pi`. Either contradicts the necessary inequalities.

Hence no such packing at `R<R_crit`. QED.

## What this changes in v27

The existing handoff describes 193 outstanding *case occurrences* whose core order
is `(10,5,7,9,2,8,6)` and whose disk-10 radial box lies inside `I`. Once this
theorem is connected as an independently replayable certificate to each original v27
case, the 159 applicable wall-push cases **and the additional 34 that failed wall-push checks** can all be covered. The 193 case occurrences are spread over two core-skeleton/mask patterns:

- `(10,7,9,8)` and `(20,1,2,40)` — 103 occurrences.
- `(10,7,9,8)` and `(24,1,2,36)` — 90 occurrences.

The four occurrences with skeleton `(10,7,8,9)` and masks `(5,16,40,2)` (3 occurrences) and `(4,16,41,2)` (1 occurrence) remain OUTSIDE this theorem.

Replaying v27 requires the original v27 tree and verification code, which were not included in the uploaded three planning documents. The exact 193 applications therefore have **not** been mechanically connected and counted as closed in a trusted replay.

## Run

```shell
python verify_radial_angle_monotonicity.py
python certified_angle_root.py
```

The first script performs **all sign/corner/triangle tests using exact Fraction arithmetic** (with integer square-root enclosures). The second script separately certifies the root and the 10-disk upper bound. Neither script proves the missing four other-order cases.
