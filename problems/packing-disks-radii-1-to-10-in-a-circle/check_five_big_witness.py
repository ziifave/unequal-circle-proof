from fractions import Fraction as F
import math,itertools
R=F('21.9');order=(10,6,9,8,7);beta=lambda i,j:2*math.asin(math.sqrt(i*j/((float(R)-i)*(float(R)-j))))
gaps=[beta(i,j) for i,j in zip(order,order[1:]+order[:1])];slack=(2*math.pi-sum(gaps))/5
pts={};ang=0
for k,i in enumerate(order):
 if k:ang+=gaps[k-1]+slack
 factor=float(R)-i-.02
 pts[i]=(F(f'{factor*math.cos(ang):.3f}'),F(f'{factor*math.sin(ang):.3f}'))
for i in order:
 x,y=pts[i];assert x*x+y*y<(R-i)**2,(i,pts[i]);print(f'radius {i}: p=({x},{y}), margin2={(R-i)**2-(x*x+y*y)}')
for i,j in itertools.combinations(order,2):
 x,y=pts[i];u,v=pts[j]
 d=(x-u)**2+(y-v)**2-(i+j)**2
 assert d>0,(i,j,d)
print('PASS exact Fraction inequalities for five circles (6..10) in radius 21.9')
