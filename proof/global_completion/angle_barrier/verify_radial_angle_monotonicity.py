"""Exact-rational certificate: the two 7-circle path angle sums decrease
coordinatewise as the six peripheral center distances increase.

Inputs: r_i=sqrt(i), R<=U=8.303468122111490, t=s_10<=1.1265,
s_i in [r_10+r_i-1.1265, U-r_i].  All actual packing configurations
satisfy these radial enclosures by the triangle inequality.  The lower
bound s_10>=0.8588 is needed in the global proof and angle-barrier step.

All TESTS in this script use integers/fractions only.  Decimals printed
below are *floored rational lower bounds* for ease of inspection.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt

Q = 10**12
T_LO, T_HI = F('0.8588'), F('1.1265')
R_HI = F('8.303468122111490')
W = (2,5,6,7,8,9)
EDGES_A = ((10,5),(5,7),(7,9),(9,2),(2,8),(8,6),(6,10))
EDGES_B = ((10,7),(7,9),(9,2),(2,8),(8,6),(6,10))

# Guaranteed outward rational approximations to sqrt(n).
def sqrt_bounds(n):
    a=isqrt(n*Q*Q)
    lo,hi=F(a,Q),F(a+1,Q)
    assert lo*lo<=n and hi*hi>n
    return lo,hi

root={i:sqrt_bounds(i) for i in range(1,11)}
l={10:T_LO}
u={10:T_HI}
for i in W:
    l[i]=root[10][0]+root[i][0]-T_HI
    u[i]=R_HI-root[i][0]
    assert 0<l[i]<u[i]

# Contact distance squares, sound lower and upper rational enclosures.
def d2lo(i,j):return (root[i][0]+root[j][0])**2
def d2hi(i,j):return (root[i][1]+root[j][1])**2

def floor_decimal(x,places=6):
    m=10**places
    return f'{x.numerator*m//x.denominator/m:.{places}f}'

# For a fixed i, derivative of necessary angle phi_ij with respect to s_i:
#   d phi_ij/ds_i = -(s_i^2-s_j^2+(ri+rj)^2)/(2*s_i^2*s_j*sin(phi_ij)).
# Thus if the signed quantity Xij in the numerator is positive then this
# piece is non-increasing; otherwise two neighboring arcs must be combined.
def Xlo(i,j): return l[i]**2-u[j]**2+d2lo(i,j)

for i,j in EDGES_A + EDGES_B:
    # |s_i-s_j| < r_i+r_j, so all angles remain well-defined during a
    # coordinatewise radial increase once s_i+s_j >= r_i+r_j initially.
    assert max(u[i]-l[j],u[j]-l[i]) < root[i][0]+root[j][0],(i,j)

# Show that the two problematic arcs (9,2) and (2,8) always have
#       0 <= cos phi <= 4/5, hence sin(phi) >= 3/5.
# cos phi <= 4/5 iff f(x,y)=x^2+y^2-(8/5)xy <= (ri+rj)^2.
# f is convex in (x,y), so its maximum over the rectangle occurs
# at one of its four corners.
for i,j in ((9,2),(2,8)):
    assert l[i]**2 + l[j]**2 > d2hi(i,j), (i,j,'cos lower')
    diffs=[]
    for x,y in product((l[i],u[i]),(l[j],u[j])):
        diffs.append(d2lo(i,j)-(x*x+y*y-F(8,5)*x*y))
    assert min(diffs)>0,(i,j,'cos upper')
    print(f'PASS pair ({i},{j}): cos(phi) in [0,4/5]; corner gap > {floor_decimal(min(diffs))}')

# Every ``good'' radial partial derivative uses X_ij>0.  When two
# neighboring terms are mixed, bound the adverse one by sin(phi)>=3/5,
# and the favorable one by sin(phi)<=1.
# i=9 has neighbors 7 (good) and 2 (possibly bad),
# i=8 has neighbors 6 (good) and 2 (possibly bad),
# i=2 has neighbors 9 (good) and 8 (possibly bad).
for i,j in ((5,10),(5,7),(7,5),(7,9),(7,10),(6,8),(6,10)):
    assert Xlo(i,j)>0,(i,j,'sign')
    print(f'PASS simple partial ({i},{j}): X> {floor_decimal(Xlo(i,j))}')
for i,good,bad in ((9,7,2),(8,6,2),(2,9,8)):
    favorable=Xlo(i,good)/u[good] # <= X/(s_good * sin(phi_good))
    adverse=max(F(0),-Xlo(i,bad))/(l[bad]*F(3,5))
    margin=favorable-adverse
    assert margin>0,(i,good,bad,'sum negative')
    print(f'PASS combined partial i={i}: favorable > {floor_decimal(favorable)}, adverse < {floor_decimal(adverse)}, margin > {floor_decimal(margin)}')

# Optional independent geometry: 7->9 requires at least 60 degrees
# (cos<=1/2), 9->2 requires > acos(4/5)>36 degrees;
# hence the 7->2 directed angular separation is >90 degrees.
gaps=[]
for x,y in product((l[7],u[7]),(l[9],u[9])):
    gaps.append(d2lo(7,9)-(x*x+y*y-x*y))
assert min(gaps)>0
print(f'PASS (7,9): cos(phi) < 1/2; corner gap > {floor_decimal(min(gaps))}')

print('CERTIFIED: A_radial and B_radial are coordinatewise non-increasing in all six outer center radii on every geometrically admissible radial segment.')
print('CONSEQUENCE: for 7.9<=R<=Rcrit, t in [0.8588,1.1265], core cyclic order (10,5,7,9,2,8,6), feasibility implies A_wall<=2*pi and B_wall<=2*pi, WITHOUT any disk motion or wall-pushing hypotheses.')
print('NOTE: This script does not certify the v27 exhaustive tree or the remaining OTHER-ORDER four cases.')
