#!/usr/bin/env python3
"""Independent modular check of characteristic-zero norm output, all 16 embeddings.
No float arithmetic; uses polynomial multiplication over F_p independently
of the GMP Kronecker-substitution norm generator.
"""
import csv
from pathlib import Path
import hashlib
import itertools
from sympy.ntheory.residue_ntheory import sqrt_mod
from sympy import Poly, symbols
from sympy.polys.polytools import gcd

BASE=Path(__file__).resolve().parents[1]
A=BASE/'data/G112_primitive_components.tsv'
P=BASE/'data/P1792_primitive_integer_coefficients.tsv'
rads=[2,3,5,7]

def csvread(path):
 with path.open() as f:
  rows=list(csv.reader(f,delimiter='\t'))
 return [list(map(int,r[1:])) for i,r in enumerate(rows[1:]) if int(r[0])==i]

def mul(a,b,p):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    c[i+j]=(c[i+j]+x*y)%p
 return c

def check(p, do_gcd=False):
 ag=csvread(A);q=csvread(P)
 assert len(ag)==113 and all(len(r)==16 for r in ag)
 assert len(q)==1793 and all(len(r)==1 for r in q)
 roots=[int(sqrt_mod(d,p)) for d in rads]
 assert all(r*r%p==d for d,r in zip(rads,roots))
 signs=list(itertools.product((1,-1),repeat=4))
 norm=[1]
 polys=[]
 for sig in signs:
  coeff=[]
  for row in ag:
   v=0
   for mask,a in enumerate(row):
    factor=a%p
    for k in range(4):
     if mask>>k&1:factor=factor*roots[k]*sig[k]%p
    v+=factor
   coeff.append(v%p)
  assert coeff[-1]%p!=0, ('bad prime: leading coefficient nonunit',p)
  polys.append(coeff)
  norm=mul(norm,coeff,p)
 assert norm[-1]%p!=0
 qcoeff=[v[0]%p for v in q]
 scale=qcoeff[-1]*pow(norm[-1],-1,p)%p
 assert all((x*scale-y)%p==0 for x,y in zip(norm,qcoeff)), 'Norm coefficients DO NOT MATCH'
 print('PASS p=',p,'1793/1793 coefficients; scaling',scale)
 if do_gcd:
  X=symbols('X')
  F=[Poly.from_list(c[::-1],X,modulus=p) for c in polys]
  numbad=0
  for i in range(16):
   for j in range(i+1,16):
    if gcd(F[i],F[j]).degree()!=0:numbad+=1
  assert numbad==0
  print('PASS all 120 pairs of 16 conjugates coprime modulo',p)
  # Check one explicitly chosen embedding (the first ++++) for irreducibility.
  print('first embedding irreducible?',F[0].is_irreducible)
  assert F[0].is_irreducible
  print('PASS: Rabin/finite field irreducibility of one conjugate')
 return p

if __name__=='__main__':
 print('P sha256',hashlib.sha256(P.read_bytes()).hexdigest())
 check(10391,True)
 check(1129,False)
