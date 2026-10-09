"""Recover the r_i=sqrt(i), n=10 candidate packing radius from the
7-circle rigid contact core, using a single algebraic closure equation.

This DOES NOT compute a minimal polynomial or certify global optimality.
Everything in closure(R) is algebraic in R: asin/exp merely choose the
real geometric branch of a square-root algebraic expression.

Verified against E. Specht's Packomania ccir10 (as of 2026-10-08).
"""
from itertools import combinations
import mpmath as mp

mp.mp.dps = 220
r = lambda i: mp.sqrt(i)

# The triangle of mutually tangent disks (5,7,10) is rigid.
d57 = r(5)+r(7)
d710 = r(7)+r(10)
d510 = r(5)+r(10)
lam = (d710**2 + d57**2 - d510**2)/(2*d57**2)
mu = 2*mp.sqrt(r(5)*r(7)*r(10)*(r(5)+r(7)+r(10)))/d57**2

CHAIN = ((7,9),(9,2),(2,8),(8,6))
CONTACTS = {(2,8),(2,9),(5,7),(5,10),(6,8),(6,10),(7,9),(7,10)}

def theta(R, i, j):
    """Angle between outward radii of two tangent boundary disks."""
    t_i, t_j = R-r(i), R-r(j)
    return 2*mp.asin(mp.sqrt(r(i)*r(j)/(t_i*t_j)))

def core(R):
    """Geometric branch matching Packomania; disk 7 lies on positive x axis."""
    u = {7: mp.mpc(R-r(7))}
    u[5] = (R-r(5))*mp.exp(1j*theta(R,5,7))
    phase = mp.mpf(0)
    for i,j in CHAIN:
        phase += theta(R,i,j)
        u[j] = (R-r(j))*mp.exp(-1j*phase)
    u[10] = u[7]+(lam+1j*mu)*(u[5]-u[7])
    return u

def closure(R):
    u = core(R)
    return abs(u[6]-u[10])**2-(r(6)+r(10))**2

R0 = mp.findroot(closure, (mp.mpf('8.30346812'), mp.mpf('8.30346813')))
print('R0 candidate =', mp.nstr(R0, 165))
print('closure residual =', mp.nstr(closure(R0), 8))

u = core(R0)
wall = (2,5,6,7,8,9)
worst_wall = max(abs(abs(u[i])+r(i)-R0) for i in wall)
worst_contact = max(abs(abs(u[i]-u[j])-(r(i)+r(j))) for i,j in CONTACTS)
slacks = [(abs(u[i]-u[j])-(r(i)+r(j)),i,j)
          for i,j in combinations(sorted(u),2) if (i,j) not in CONTACTS]
print('max wall contact residual =', mp.nstr(worst_wall, 8))
print('max pair contact residual =', mp.nstr(worst_contact, 8))
print('min noncontact gap =', mp.nstr(min(slacks)[0], 25),
      'for', min(slacks)[1:])
print('disk 10 boundary slack =', mp.nstr(R0-abs(u[10])-r(10), 18))

# Numerical-only probe; absence of relations is NOT a mathematical
# lower bound on the algebraic degree. Use high precision to avoid
# spurious PSLQ relations.
print('Integer polynomial relation search: powers of (R0-8), degree <= 12, |coeff| <= 10^8')
powers=[mp.mpf(1)]
for deg in range(1,13):
    powers.append(powers[-1]*(R0-8))
    relation=mp.pslq(mp.matrix(powers),tol=mp.mpf('1e-175'),maxcoeff=10**8,maxsteps=2000)
    if relation:
        residual=sum(a*p for a,p in zip(relation,powers))
        print('Possible relation:',deg,relation,'residual',mp.nstr(residual,12))
    else:
        print(f'degree {deg}: no relation detected')
