"""Direct integer-only test of P1792 values and a derivative bound.
Checks existence and, if bound succeeds, uniqueness of *a root of P* in
[a,b], as an independent algebraic witness. This does not identify the
P-root with the contact closure root without an elimination theorem.
"""
from pathlib import Path
from fractions import Fraction
import csv
import sys
sys.set_int_max_str_digits(0)

BASE=Path(__file__).resolve().parents[1]
P=BASE/'data/P1792_primitive_integer_coefficients.tsv'
with P.open() as f:rows=list(csv.DictReader(f,delimiter='\t'))
c=[int(r['coefficient']) for r in rows]
assert len(c)==1793
N=len(c)-1

def scaled_eval(coef,A,B):
    v=coef[-1];power=B
    for i in range(len(coef)-2,-1,-1):
        v=v*A+coef[i]*power
        power*=B
    return v

def sgn(n):return (n>0)-(n<0)
low='8.3034681221114890787043811875161993'
high='8.3034681221114890787043811875161994'
assert len(low.split('.')[1])==len(high.split('.')[1])
B=10**len(low.split('.')[1]);Al=int(low.replace('.',''));Ah=int(high.replace('.',''))
L=scaled_eval(c,Al,B)
H=scaled_eval(c,Ah,B)
print('P(low) sign',sgn(L),'P(high) sign',sgn(H), 'integer evaluation exact')
print('numerator decimals length at left/right',len(str(abs(L))),len(str(abs(H))))
print('denominator exponent',len(str(B**N)))
assert L!=0 and H!=0 and L*H<0
print('PASS: at least one real P-root in [low,high] by IVT')
cp=[i*c[i] for i in range(1,len(c))]
D=scaled_eval(cp,Al,B)
print('P\'(low) sign',sgn(D),'scaled log10 magnitude',len(str(abs(D)))-1)
# crude global bound for |P''(t)| on [low,high] subset [0,9]
M2=sum(abs(c[i])*i*(i-1)*pow(9,i-2) for i in range(2,N+1))
print('M2 magnitude digits',len(str(M2)))
# Compare |P'(low)| > width * sup |P''| via strictly integer arithmetic.
# P'(low) = D/B^(N-1), width = (Ah-Al)/B.
left=abs(D)
right=(Ah-Al)*M2*pow(B,N-2)
print('simple derivative bound succeeds?',left>right)
if left>right:
 print('PASS: P derivative has constant nonzero sign throughout [low, high]; exactly one root')
else:
 print('INCONCLUSIVE: cannot prove uniqueness with simple global derivative bound')

# Stronger Taylor-center bound for derivative variation.
# P'(a+delta) = sum_{k=0}^m C_k delta^k + T_m(delta).
# C_k = sum_{j=k+1}^N j * binom(j-1,k) * c_j * a^(j-1-k)
# |T_m(delta)| <= delta^(m+1)*sum_j |j*c_j|*10^(j-1),
# since 0<=a<9, 0<=delta<=1/B and (a+1)<=10.
from math import comb
m=10
D0=D
variation=0
for k in range(1,m+1):
    coeff=[(i+k+1)*comb(i+k,k)*c[i+k+1] for i in range(N-k)]
    Tk=scaled_eval(coeff,Al,B)
    variation+=abs(Tk)*pow(Ah-Al,k)
    print('Taylor term',k,'numerator digits',len(str(abs(Tk))) if Tk else 0)
Mb=sum(abs(i*c[i])*pow(10,i-1) for i in range(1,N+1))
tail=Mb*pow(Ah-Al,m+1)*pow(B,N-m-2)
print('P derivative center sign',sgn(D0))
print('Dominance: |P\'(low)| scaled > variation+tail ?',abs(D0)>variation+tail)
assert abs(D0)>variation+tail
print('PASS: rational Taylor certificate P\' strictly positive on [low,high]')
print('PASS: exactly one real root of P in rational interval, entirely integer arithmetic')
